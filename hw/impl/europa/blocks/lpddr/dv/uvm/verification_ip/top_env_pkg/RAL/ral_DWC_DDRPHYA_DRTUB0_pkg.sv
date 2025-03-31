`ifndef RAL_DWC_DDRPHYA_DRTUB0_PKG
`define RAL_DWC_DDRPHYA_DRTUB0_PKG

package ral_DWC_DDRPHYA_DRTUB0_pkg;
import uvm_pkg::*;

class ral_reg_DWC_DDRPHYA_DRTUB0_PieVecCfg extends uvm_reg;
	rand uvm_reg_field PieInitStartVec0;
	rand uvm_reg_field PieInitStartVec1;
	rand uvm_reg_field PieInitStartVec2;
	rand uvm_reg_field PieInitStartVec3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PieInitStartVec0: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   PieInitStartVec1: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   PieInitStartVec2: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   PieInitStartVec3: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_DRTUB0_PieVecCfg");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PieInitStartVec0 = uvm_reg_field::type_id::create("PieInitStartVec0",,get_full_name());
      this.PieInitStartVec0.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.PieInitStartVec1 = uvm_reg_field::type_id::create("PieInitStartVec1",,get_full_name());
      this.PieInitStartVec1.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.PieInitStartVec2 = uvm_reg_field::type_id::create("PieInitStartVec2",,get_full_name());
      this.PieInitStartVec2.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.PieInitStartVec3 = uvm_reg_field::type_id::create("PieInitStartVec3",,get_full_name());
      this.PieInitStartVec3.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_PieVecCfg)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_PieVecCfg


class ral_reg_DWC_DDRPHYA_DRTUB0_PieInitVecSel extends uvm_reg;
	rand uvm_reg_field PieInitVecSel0;
	rand uvm_reg_field PieInitVecSel1;
	rand uvm_reg_field PieInitVecSel2;
	rand uvm_reg_field PieInitVecSel3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PieInitVecSel0: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   PieInitVecSel1: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   PieInitVecSel2: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   PieInitVecSel3: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_DRTUB0_PieInitVecSel");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PieInitVecSel0 = uvm_reg_field::type_id::create("PieInitVecSel0",,get_full_name());
      this.PieInitVecSel0.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.PieInitVecSel1 = uvm_reg_field::type_id::create("PieInitVecSel1",,get_full_name());
      this.PieInitVecSel1.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.PieInitVecSel2 = uvm_reg_field::type_id::create("PieInitVecSel2",,get_full_name());
      this.PieInitVecSel2.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.PieInitVecSel3 = uvm_reg_field::type_id::create("PieInitVecSel3",,get_full_name());
      this.PieInitVecSel3.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_PieInitVecSel)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_PieInitVecSel


class ral_reg_DWC_DDRPHYA_DRTUB0_DctShadowRegs extends uvm_reg;
	uvm_reg_field DctShadowRegs;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DctShadowRegs: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_DctShadowRegs");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DctShadowRegs = uvm_reg_field::type_id::create("DctShadowRegs",,get_full_name());
      this.DctShadowRegs.configure(this, 1, 0, "RO", 1, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_DctShadowRegs)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_DctShadowRegs


class ral_reg_DWC_DDRPHYA_DRTUB0_DctWriteOnlyShadow extends uvm_reg;
	uvm_reg_field DctWriteOnlyShadow;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DctWriteOnlyShadow: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {17'b???????????????00};
	      wildcard bins bit_0_wr_as_1 = {17'b???????????????10};
	      wildcard bins bit_0_rd = {17'b????????????????1};
	      wildcard bins bit_1_wr_as_0 = {17'b??????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {17'b??????????????1?0};
	      wildcard bins bit_1_rd = {17'b????????????????1};
	      wildcard bins bit_2_wr_as_0 = {17'b?????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {17'b?????????????1??0};
	      wildcard bins bit_2_rd = {17'b????????????????1};
	      wildcard bins bit_3_wr_as_0 = {17'b????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {17'b????????????1???0};
	      wildcard bins bit_3_rd = {17'b????????????????1};
	      wildcard bins bit_4_wr_as_0 = {17'b???????????0????0};
	      wildcard bins bit_4_wr_as_1 = {17'b???????????1????0};
	      wildcard bins bit_4_rd = {17'b????????????????1};
	      wildcard bins bit_5_wr_as_0 = {17'b??????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {17'b??????????1?????0};
	      wildcard bins bit_5_rd = {17'b????????????????1};
	      wildcard bins bit_6_wr_as_0 = {17'b?????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {17'b?????????1??????0};
	      wildcard bins bit_6_rd = {17'b????????????????1};
	      wildcard bins bit_7_wr_as_0 = {17'b????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {17'b????????1???????0};
	      wildcard bins bit_7_rd = {17'b????????????????1};
	      wildcard bins bit_8_wr_as_0 = {17'b???????0????????0};
	      wildcard bins bit_8_wr_as_1 = {17'b???????1????????0};
	      wildcard bins bit_8_rd = {17'b????????????????1};
	      wildcard bins bit_9_wr_as_0 = {17'b??????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {17'b??????1?????????0};
	      wildcard bins bit_9_rd = {17'b????????????????1};
	      wildcard bins bit_10_wr_as_0 = {17'b?????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {17'b?????1??????????0};
	      wildcard bins bit_10_rd = {17'b????????????????1};
	      wildcard bins bit_11_wr_as_0 = {17'b????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {17'b????1???????????0};
	      wildcard bins bit_11_rd = {17'b????????????????1};
	      wildcard bins bit_12_wr_as_0 = {17'b???0????????????0};
	      wildcard bins bit_12_wr_as_1 = {17'b???1????????????0};
	      wildcard bins bit_12_rd = {17'b????????????????1};
	      wildcard bins bit_13_wr_as_0 = {17'b??0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {17'b??1?????????????0};
	      wildcard bins bit_13_rd = {17'b????????????????1};
	      wildcard bins bit_14_wr_as_0 = {17'b?0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {17'b?1??????????????0};
	      wildcard bins bit_14_rd = {17'b????????????????1};
	      wildcard bins bit_15_wr_as_0 = {17'b0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {17'b1???????????????0};
	      wildcard bins bit_15_rd = {17'b????????????????1};
	      option.weight = 48;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_DctWriteOnlyShadow");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DctWriteOnlyShadow = uvm_reg_field::type_id::create("DctWriteOnlyShadow",,get_full_name());
      this.DctWriteOnlyShadow.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_DctWriteOnlyShadow)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_DctWriteOnlyShadow


class ral_reg_DWC_DDRPHYA_DRTUB0_UctWriteOnly extends uvm_reg;
	rand uvm_reg_field UctWriteOnly;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   UctWriteOnly: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {17'b???????????????00};
	      wildcard bins bit_0_wr_as_1 = {17'b???????????????10};
	      wildcard bins bit_0_rd_as_0 = {17'b???????????????01};
	      wildcard bins bit_0_rd_as_1 = {17'b???????????????11};
	      wildcard bins bit_1_wr_as_0 = {17'b??????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {17'b??????????????1?0};
	      wildcard bins bit_1_rd_as_0 = {17'b??????????????0?1};
	      wildcard bins bit_1_rd_as_1 = {17'b??????????????1?1};
	      wildcard bins bit_2_wr_as_0 = {17'b?????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {17'b?????????????1??0};
	      wildcard bins bit_2_rd_as_0 = {17'b?????????????0??1};
	      wildcard bins bit_2_rd_as_1 = {17'b?????????????1??1};
	      wildcard bins bit_3_wr_as_0 = {17'b????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {17'b????????????1???0};
	      wildcard bins bit_3_rd_as_0 = {17'b????????????0???1};
	      wildcard bins bit_3_rd_as_1 = {17'b????????????1???1};
	      wildcard bins bit_4_wr_as_0 = {17'b???????????0????0};
	      wildcard bins bit_4_wr_as_1 = {17'b???????????1????0};
	      wildcard bins bit_4_rd_as_0 = {17'b???????????0????1};
	      wildcard bins bit_4_rd_as_1 = {17'b???????????1????1};
	      wildcard bins bit_5_wr_as_0 = {17'b??????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {17'b??????????1?????0};
	      wildcard bins bit_5_rd_as_0 = {17'b??????????0?????1};
	      wildcard bins bit_5_rd_as_1 = {17'b??????????1?????1};
	      wildcard bins bit_6_wr_as_0 = {17'b?????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {17'b?????????1??????0};
	      wildcard bins bit_6_rd_as_0 = {17'b?????????0??????1};
	      wildcard bins bit_6_rd_as_1 = {17'b?????????1??????1};
	      wildcard bins bit_7_wr_as_0 = {17'b????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {17'b????????1???????0};
	      wildcard bins bit_7_rd_as_0 = {17'b????????0???????1};
	      wildcard bins bit_7_rd_as_1 = {17'b????????1???????1};
	      wildcard bins bit_8_wr_as_0 = {17'b???????0????????0};
	      wildcard bins bit_8_wr_as_1 = {17'b???????1????????0};
	      wildcard bins bit_8_rd_as_0 = {17'b???????0????????1};
	      wildcard bins bit_8_rd_as_1 = {17'b???????1????????1};
	      wildcard bins bit_9_wr_as_0 = {17'b??????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {17'b??????1?????????0};
	      wildcard bins bit_9_rd_as_0 = {17'b??????0?????????1};
	      wildcard bins bit_9_rd_as_1 = {17'b??????1?????????1};
	      wildcard bins bit_10_wr_as_0 = {17'b?????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {17'b?????1??????????0};
	      wildcard bins bit_10_rd_as_0 = {17'b?????0??????????1};
	      wildcard bins bit_10_rd_as_1 = {17'b?????1??????????1};
	      wildcard bins bit_11_wr_as_0 = {17'b????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {17'b????1???????????0};
	      wildcard bins bit_11_rd_as_0 = {17'b????0???????????1};
	      wildcard bins bit_11_rd_as_1 = {17'b????1???????????1};
	      wildcard bins bit_12_wr_as_0 = {17'b???0????????????0};
	      wildcard bins bit_12_wr_as_1 = {17'b???1????????????0};
	      wildcard bins bit_12_rd_as_0 = {17'b???0????????????1};
	      wildcard bins bit_12_rd_as_1 = {17'b???1????????????1};
	      wildcard bins bit_13_wr_as_0 = {17'b??0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {17'b??1?????????????0};
	      wildcard bins bit_13_rd_as_0 = {17'b??0?????????????1};
	      wildcard bins bit_13_rd_as_1 = {17'b??1?????????????1};
	      wildcard bins bit_14_wr_as_0 = {17'b?0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {17'b?1??????????????0};
	      wildcard bins bit_14_rd_as_0 = {17'b?0??????????????1};
	      wildcard bins bit_14_rd_as_1 = {17'b?1??????????????1};
	      wildcard bins bit_15_wr_as_0 = {17'b0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {17'b1???????????????0};
	      wildcard bins bit_15_rd_as_0 = {17'b0???????????????1};
	      wildcard bins bit_15_rd_as_1 = {17'b1???????????????1};
	      option.weight = 64;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_UctWriteOnly");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.UctWriteOnly = uvm_reg_field::type_id::create("UctWriteOnly",,get_full_name());
      this.UctWriteOnly.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_UctWriteOnly)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_UctWriteOnly


class ral_reg_DWC_DDRPHYA_DRTUB0_UctWriteProt extends uvm_reg;
	rand uvm_reg_field UctWriteProt;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   UctWriteProt: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_UctWriteProt");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.UctWriteProt = uvm_reg_field::type_id::create("UctWriteProt",,get_full_name());
      this.UctWriteProt.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_UctWriteProt)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_UctWriteProt


class ral_reg_DWC_DDRPHYA_DRTUB0_UctDatWriteOnly extends uvm_reg;
	rand uvm_reg_field UctDatWriteOnly;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   UctDatWriteOnly: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {17'b???????????????00};
	      wildcard bins bit_0_wr_as_1 = {17'b???????????????10};
	      wildcard bins bit_0_rd_as_0 = {17'b???????????????01};
	      wildcard bins bit_0_rd_as_1 = {17'b???????????????11};
	      wildcard bins bit_1_wr_as_0 = {17'b??????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {17'b??????????????1?0};
	      wildcard bins bit_1_rd_as_0 = {17'b??????????????0?1};
	      wildcard bins bit_1_rd_as_1 = {17'b??????????????1?1};
	      wildcard bins bit_2_wr_as_0 = {17'b?????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {17'b?????????????1??0};
	      wildcard bins bit_2_rd_as_0 = {17'b?????????????0??1};
	      wildcard bins bit_2_rd_as_1 = {17'b?????????????1??1};
	      wildcard bins bit_3_wr_as_0 = {17'b????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {17'b????????????1???0};
	      wildcard bins bit_3_rd_as_0 = {17'b????????????0???1};
	      wildcard bins bit_3_rd_as_1 = {17'b????????????1???1};
	      wildcard bins bit_4_wr_as_0 = {17'b???????????0????0};
	      wildcard bins bit_4_wr_as_1 = {17'b???????????1????0};
	      wildcard bins bit_4_rd_as_0 = {17'b???????????0????1};
	      wildcard bins bit_4_rd_as_1 = {17'b???????????1????1};
	      wildcard bins bit_5_wr_as_0 = {17'b??????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {17'b??????????1?????0};
	      wildcard bins bit_5_rd_as_0 = {17'b??????????0?????1};
	      wildcard bins bit_5_rd_as_1 = {17'b??????????1?????1};
	      wildcard bins bit_6_wr_as_0 = {17'b?????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {17'b?????????1??????0};
	      wildcard bins bit_6_rd_as_0 = {17'b?????????0??????1};
	      wildcard bins bit_6_rd_as_1 = {17'b?????????1??????1};
	      wildcard bins bit_7_wr_as_0 = {17'b????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {17'b????????1???????0};
	      wildcard bins bit_7_rd_as_0 = {17'b????????0???????1};
	      wildcard bins bit_7_rd_as_1 = {17'b????????1???????1};
	      wildcard bins bit_8_wr_as_0 = {17'b???????0????????0};
	      wildcard bins bit_8_wr_as_1 = {17'b???????1????????0};
	      wildcard bins bit_8_rd_as_0 = {17'b???????0????????1};
	      wildcard bins bit_8_rd_as_1 = {17'b???????1????????1};
	      wildcard bins bit_9_wr_as_0 = {17'b??????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {17'b??????1?????????0};
	      wildcard bins bit_9_rd_as_0 = {17'b??????0?????????1};
	      wildcard bins bit_9_rd_as_1 = {17'b??????1?????????1};
	      wildcard bins bit_10_wr_as_0 = {17'b?????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {17'b?????1??????????0};
	      wildcard bins bit_10_rd_as_0 = {17'b?????0??????????1};
	      wildcard bins bit_10_rd_as_1 = {17'b?????1??????????1};
	      wildcard bins bit_11_wr_as_0 = {17'b????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {17'b????1???????????0};
	      wildcard bins bit_11_rd_as_0 = {17'b????0???????????1};
	      wildcard bins bit_11_rd_as_1 = {17'b????1???????????1};
	      wildcard bins bit_12_wr_as_0 = {17'b???0????????????0};
	      wildcard bins bit_12_wr_as_1 = {17'b???1????????????0};
	      wildcard bins bit_12_rd_as_0 = {17'b???0????????????1};
	      wildcard bins bit_12_rd_as_1 = {17'b???1????????????1};
	      wildcard bins bit_13_wr_as_0 = {17'b??0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {17'b??1?????????????0};
	      wildcard bins bit_13_rd_as_0 = {17'b??0?????????????1};
	      wildcard bins bit_13_rd_as_1 = {17'b??1?????????????1};
	      wildcard bins bit_14_wr_as_0 = {17'b?0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {17'b?1??????????????0};
	      wildcard bins bit_14_rd_as_0 = {17'b?0??????????????1};
	      wildcard bins bit_14_rd_as_1 = {17'b?1??????????????1};
	      wildcard bins bit_15_wr_as_0 = {17'b0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {17'b1???????????????0};
	      wildcard bins bit_15_rd_as_0 = {17'b0???????????????1};
	      wildcard bins bit_15_rd_as_1 = {17'b1???????????????1};
	      option.weight = 64;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_UctDatWriteOnly");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.UctDatWriteOnly = uvm_reg_field::type_id::create("UctDatWriteOnly",,get_full_name());
      this.UctDatWriteOnly.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_UctDatWriteOnly)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_UctDatWriteOnly


class ral_reg_DWC_DDRPHYA_DRTUB0_UctDatWriteProt extends uvm_reg;
	rand uvm_reg_field UctDatWriteProt;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   UctDatWriteProt: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_UctDatWriteProt");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.UctDatWriteProt = uvm_reg_field::type_id::create("UctDatWriteProt",,get_full_name());
      this.UctDatWriteProt.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_UctDatWriteProt)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_UctDatWriteProt


class ral_reg_DWC_DDRPHYA_DRTUB0_UctlErr extends uvm_reg;
	rand uvm_reg_field UctlErr;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   UctlErr: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_UctlErr");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.UctlErr = uvm_reg_field::type_id::create("UctlErr",,get_full_name());
      this.UctlErr.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_UctlErr)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_UctlErr


class ral_reg_DWC_DDRPHYA_DRTUB0_DRTUBParityInvert extends uvm_reg;
	rand uvm_reg_field DRTUBParityInvert;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DRTUBParityInvert: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {3'b?00};
	      wildcard bins bit_0_wr_as_1 = {3'b?10};
	      wildcard bins bit_0_rd_as_0 = {3'b?01};
	      wildcard bins bit_0_rd_as_1 = {3'b?11};
	      wildcard bins bit_1_wr_as_0 = {3'b0?0};
	      wildcard bins bit_1_wr_as_1 = {3'b1?0};
	      wildcard bins bit_1_rd_as_0 = {3'b0?1};
	      wildcard bins bit_1_rd_as_1 = {3'b1?1};
	      option.weight = 8;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_DRTUBParityInvert");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DRTUBParityInvert = uvm_reg_field::type_id::create("DRTUBParityInvert",,get_full_name());
      this.DRTUBParityInvert.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_DRTUBParityInvert)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_DRTUBParityInvert


class ral_reg_DWC_DDRPHYA_DRTUB0_UCParityInvert extends uvm_reg;
	rand uvm_reg_field UCParityInvert;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   UCParityInvert: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_DRTUB0_UCParityInvert");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.UCParityInvert = uvm_reg_field::type_id::create("UCParityInvert",,get_full_name());
      this.UCParityInvert.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_UCParityInvert)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_UCParityInvert


class ral_reg_DWC_DDRPHYA_DRTUB0_ScratchPadDRTUB extends uvm_reg;
	rand uvm_reg_field ScratchPadDRTUB;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ScratchPadDRTUB: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {17'b???????????????00};
	      wildcard bins bit_0_wr_as_1 = {17'b???????????????10};
	      wildcard bins bit_0_rd_as_0 = {17'b???????????????01};
	      wildcard bins bit_0_rd_as_1 = {17'b???????????????11};
	      wildcard bins bit_1_wr_as_0 = {17'b??????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {17'b??????????????1?0};
	      wildcard bins bit_1_rd_as_0 = {17'b??????????????0?1};
	      wildcard bins bit_1_rd_as_1 = {17'b??????????????1?1};
	      wildcard bins bit_2_wr_as_0 = {17'b?????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {17'b?????????????1??0};
	      wildcard bins bit_2_rd_as_0 = {17'b?????????????0??1};
	      wildcard bins bit_2_rd_as_1 = {17'b?????????????1??1};
	      wildcard bins bit_3_wr_as_0 = {17'b????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {17'b????????????1???0};
	      wildcard bins bit_3_rd_as_0 = {17'b????????????0???1};
	      wildcard bins bit_3_rd_as_1 = {17'b????????????1???1};
	      wildcard bins bit_4_wr_as_0 = {17'b???????????0????0};
	      wildcard bins bit_4_wr_as_1 = {17'b???????????1????0};
	      wildcard bins bit_4_rd_as_0 = {17'b???????????0????1};
	      wildcard bins bit_4_rd_as_1 = {17'b???????????1????1};
	      wildcard bins bit_5_wr_as_0 = {17'b??????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {17'b??????????1?????0};
	      wildcard bins bit_5_rd_as_0 = {17'b??????????0?????1};
	      wildcard bins bit_5_rd_as_1 = {17'b??????????1?????1};
	      wildcard bins bit_6_wr_as_0 = {17'b?????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {17'b?????????1??????0};
	      wildcard bins bit_6_rd_as_0 = {17'b?????????0??????1};
	      wildcard bins bit_6_rd_as_1 = {17'b?????????1??????1};
	      wildcard bins bit_7_wr_as_0 = {17'b????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {17'b????????1???????0};
	      wildcard bins bit_7_rd_as_0 = {17'b????????0???????1};
	      wildcard bins bit_7_rd_as_1 = {17'b????????1???????1};
	      wildcard bins bit_8_wr_as_0 = {17'b???????0????????0};
	      wildcard bins bit_8_wr_as_1 = {17'b???????1????????0};
	      wildcard bins bit_8_rd_as_0 = {17'b???????0????????1};
	      wildcard bins bit_8_rd_as_1 = {17'b???????1????????1};
	      wildcard bins bit_9_wr_as_0 = {17'b??????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {17'b??????1?????????0};
	      wildcard bins bit_9_rd_as_0 = {17'b??????0?????????1};
	      wildcard bins bit_9_rd_as_1 = {17'b??????1?????????1};
	      wildcard bins bit_10_wr_as_0 = {17'b?????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {17'b?????1??????????0};
	      wildcard bins bit_10_rd_as_0 = {17'b?????0??????????1};
	      wildcard bins bit_10_rd_as_1 = {17'b?????1??????????1};
	      wildcard bins bit_11_wr_as_0 = {17'b????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {17'b????1???????????0};
	      wildcard bins bit_11_rd_as_0 = {17'b????0???????????1};
	      wildcard bins bit_11_rd_as_1 = {17'b????1???????????1};
	      wildcard bins bit_12_wr_as_0 = {17'b???0????????????0};
	      wildcard bins bit_12_wr_as_1 = {17'b???1????????????0};
	      wildcard bins bit_12_rd_as_0 = {17'b???0????????????1};
	      wildcard bins bit_12_rd_as_1 = {17'b???1????????????1};
	      wildcard bins bit_13_wr_as_0 = {17'b??0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {17'b??1?????????????0};
	      wildcard bins bit_13_rd_as_0 = {17'b??0?????????????1};
	      wildcard bins bit_13_rd_as_1 = {17'b??1?????????????1};
	      wildcard bins bit_14_wr_as_0 = {17'b?0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {17'b?1??????????????0};
	      wildcard bins bit_14_rd_as_0 = {17'b?0??????????????1};
	      wildcard bins bit_14_rd_as_1 = {17'b?1??????????????1};
	      wildcard bins bit_15_wr_as_0 = {17'b0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {17'b1???????????????0};
	      wildcard bins bit_15_rd_as_0 = {17'b0???????????????1};
	      wildcard bins bit_15_rd_as_1 = {17'b1???????????????1};
	      option.weight = 64;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_ScratchPadDRTUB");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ScratchPadDRTUB = uvm_reg_field::type_id::create("ScratchPadDRTUB",,get_full_name());
      this.ScratchPadDRTUB.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_ScratchPadDRTUB)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_ScratchPadDRTUB


class ral_reg_DWC_DDRPHYA_DRTUB0_UcclkHclkEnables extends uvm_reg;
	rand uvm_reg_field UcclkEn;
	rand uvm_reg_field HclkEn;
	rand uvm_reg_field UcclkFull;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   UcclkEn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   HclkEn: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   UcclkFull: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_UcclkHclkEnables");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.UcclkEn = uvm_reg_field::type_id::create("UcclkEn",,get_full_name());
      this.UcclkEn.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 0);
      this.HclkEn = uvm_reg_field::type_id::create("HclkEn",,get_full_name());
      this.HclkEn.configure(this, 1, 1, "RW", 0, 1'h1, 1, 0, 0);
      this.UcclkFull = uvm_reg_field::type_id::create("UcclkFull",,get_full_name());
      this.UcclkFull.configure(this, 1, 2, "RW", 0, 1'h1, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_UcclkHclkEnables)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_UcclkHclkEnables


class ral_reg_DWC_DDRPHYA_DRTUB0_ArcEccIndications extends uvm_reg;
	uvm_reg_field ArcDccmDbError;
	uvm_reg_field ArcIccmDbError;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ArcDccmDbError: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   ArcIccmDbError: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_ArcEccIndications");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ArcDccmDbError = uvm_reg_field::type_id::create("ArcDccmDbError",,get_full_name());
      this.ArcDccmDbError.configure(this, 1, 0, "RO", 1, 1'h0, 1, 0, 0);
      this.ArcIccmDbError = uvm_reg_field::type_id::create("ArcIccmDbError",,get_full_name());
      this.ArcIccmDbError.configure(this, 1, 1, "RO", 1, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_ArcEccIndications)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_ArcEccIndications


class ral_reg_DWC_DDRPHYA_DRTUB0_ArcIccmSbErrCtr extends uvm_reg;
	uvm_reg_field ArcIccmSbErrCtr;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ArcIccmSbErrCtr: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {17'b???????????????00};
	      wildcard bins bit_0_wr_as_1 = {17'b???????????????10};
	      wildcard bins bit_0_rd = {17'b????????????????1};
	      wildcard bins bit_1_wr_as_0 = {17'b??????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {17'b??????????????1?0};
	      wildcard bins bit_1_rd = {17'b????????????????1};
	      wildcard bins bit_2_wr_as_0 = {17'b?????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {17'b?????????????1??0};
	      wildcard bins bit_2_rd = {17'b????????????????1};
	      wildcard bins bit_3_wr_as_0 = {17'b????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {17'b????????????1???0};
	      wildcard bins bit_3_rd = {17'b????????????????1};
	      wildcard bins bit_4_wr_as_0 = {17'b???????????0????0};
	      wildcard bins bit_4_wr_as_1 = {17'b???????????1????0};
	      wildcard bins bit_4_rd = {17'b????????????????1};
	      wildcard bins bit_5_wr_as_0 = {17'b??????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {17'b??????????1?????0};
	      wildcard bins bit_5_rd = {17'b????????????????1};
	      wildcard bins bit_6_wr_as_0 = {17'b?????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {17'b?????????1??????0};
	      wildcard bins bit_6_rd = {17'b????????????????1};
	      wildcard bins bit_7_wr_as_0 = {17'b????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {17'b????????1???????0};
	      wildcard bins bit_7_rd = {17'b????????????????1};
	      wildcard bins bit_8_wr_as_0 = {17'b???????0????????0};
	      wildcard bins bit_8_wr_as_1 = {17'b???????1????????0};
	      wildcard bins bit_8_rd = {17'b????????????????1};
	      wildcard bins bit_9_wr_as_0 = {17'b??????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {17'b??????1?????????0};
	      wildcard bins bit_9_rd = {17'b????????????????1};
	      wildcard bins bit_10_wr_as_0 = {17'b?????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {17'b?????1??????????0};
	      wildcard bins bit_10_rd = {17'b????????????????1};
	      wildcard bins bit_11_wr_as_0 = {17'b????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {17'b????1???????????0};
	      wildcard bins bit_11_rd = {17'b????????????????1};
	      wildcard bins bit_12_wr_as_0 = {17'b???0????????????0};
	      wildcard bins bit_12_wr_as_1 = {17'b???1????????????0};
	      wildcard bins bit_12_rd = {17'b????????????????1};
	      wildcard bins bit_13_wr_as_0 = {17'b??0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {17'b??1?????????????0};
	      wildcard bins bit_13_rd = {17'b????????????????1};
	      wildcard bins bit_14_wr_as_0 = {17'b?0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {17'b?1??????????????0};
	      wildcard bins bit_14_rd = {17'b????????????????1};
	      wildcard bins bit_15_wr_as_0 = {17'b0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {17'b1???????????????0};
	      wildcard bins bit_15_rd = {17'b????????????????1};
	      option.weight = 48;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_ArcIccmSbErrCtr");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ArcIccmSbErrCtr = uvm_reg_field::type_id::create("ArcIccmSbErrCtr",,get_full_name());
      this.ArcIccmSbErrCtr.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_ArcIccmSbErrCtr)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_ArcIccmSbErrCtr


class ral_reg_DWC_DDRPHYA_DRTUB0_ArcDccmSbErrCtr extends uvm_reg;
	uvm_reg_field ArcDccmSbErrCtr;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ArcDccmSbErrCtr: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {17'b???????????????00};
	      wildcard bins bit_0_wr_as_1 = {17'b???????????????10};
	      wildcard bins bit_0_rd = {17'b????????????????1};
	      wildcard bins bit_1_wr_as_0 = {17'b??????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {17'b??????????????1?0};
	      wildcard bins bit_1_rd = {17'b????????????????1};
	      wildcard bins bit_2_wr_as_0 = {17'b?????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {17'b?????????????1??0};
	      wildcard bins bit_2_rd = {17'b????????????????1};
	      wildcard bins bit_3_wr_as_0 = {17'b????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {17'b????????????1???0};
	      wildcard bins bit_3_rd = {17'b????????????????1};
	      wildcard bins bit_4_wr_as_0 = {17'b???????????0????0};
	      wildcard bins bit_4_wr_as_1 = {17'b???????????1????0};
	      wildcard bins bit_4_rd = {17'b????????????????1};
	      wildcard bins bit_5_wr_as_0 = {17'b??????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {17'b??????????1?????0};
	      wildcard bins bit_5_rd = {17'b????????????????1};
	      wildcard bins bit_6_wr_as_0 = {17'b?????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {17'b?????????1??????0};
	      wildcard bins bit_6_rd = {17'b????????????????1};
	      wildcard bins bit_7_wr_as_0 = {17'b????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {17'b????????1???????0};
	      wildcard bins bit_7_rd = {17'b????????????????1};
	      wildcard bins bit_8_wr_as_0 = {17'b???????0????????0};
	      wildcard bins bit_8_wr_as_1 = {17'b???????1????????0};
	      wildcard bins bit_8_rd = {17'b????????????????1};
	      wildcard bins bit_9_wr_as_0 = {17'b??????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {17'b??????1?????????0};
	      wildcard bins bit_9_rd = {17'b????????????????1};
	      wildcard bins bit_10_wr_as_0 = {17'b?????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {17'b?????1??????????0};
	      wildcard bins bit_10_rd = {17'b????????????????1};
	      wildcard bins bit_11_wr_as_0 = {17'b????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {17'b????1???????????0};
	      wildcard bins bit_11_rd = {17'b????????????????1};
	      wildcard bins bit_12_wr_as_0 = {17'b???0????????????0};
	      wildcard bins bit_12_wr_as_1 = {17'b???1????????????0};
	      wildcard bins bit_12_rd = {17'b????????????????1};
	      wildcard bins bit_13_wr_as_0 = {17'b??0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {17'b??1?????????????0};
	      wildcard bins bit_13_rd = {17'b????????????????1};
	      wildcard bins bit_14_wr_as_0 = {17'b?0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {17'b?1??????????????0};
	      wildcard bins bit_14_rd = {17'b????????????????1};
	      wildcard bins bit_15_wr_as_0 = {17'b0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {17'b1???????????????0};
	      wildcard bins bit_15_rd = {17'b????????????????1};
	      option.weight = 48;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_ArcDccmSbErrCtr");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ArcDccmSbErrCtr = uvm_reg_field::type_id::create("ArcDccmSbErrCtr",,get_full_name());
      this.ArcDccmSbErrCtr.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_ArcDccmSbErrCtr)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_ArcDccmSbErrCtr


class ral_reg_DWC_DDRPHYA_DRTUB0_ArcSbCtrEnables extends uvm_reg;
	rand uvm_reg_field ArcIccmSbCtrEn;
	rand uvm_reg_field ArcDccmSbCtrEn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ArcIccmSbCtrEn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ArcDccmSbCtrEn: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_ArcSbCtrEnables");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ArcIccmSbCtrEn = uvm_reg_field::type_id::create("ArcIccmSbCtrEn",,get_full_name());
      this.ArcIccmSbCtrEn.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.ArcDccmSbCtrEn = uvm_reg_field::type_id::create("ArcDccmSbCtrEn",,get_full_name());
      this.ArcDccmSbCtrEn.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_ArcSbCtrEnables)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_ArcSbCtrEnables


class ral_reg_DWC_DDRPHYA_DRTUB0_ArcPmuEccCtl extends uvm_reg;
	rand uvm_reg_field ArcPmuEccCtl;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ArcPmuEccCtl: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_DRTUB0_ArcPmuEccCtl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ArcPmuEccCtl = uvm_reg_field::type_id::create("ArcPmuEccCtl",,get_full_name());
      this.ArcPmuEccCtl.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_ArcPmuEccCtl)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_ArcPmuEccCtl


class ral_reg_DWC_DDRPHYA_DRTUB0_StartDCCMClear extends uvm_reg;
	rand uvm_reg_field StartDCCMClear;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   StartDCCMClear: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_StartDCCMClear");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.StartDCCMClear = uvm_reg_field::type_id::create("StartDCCMClear",,get_full_name());
      this.StartDCCMClear.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_StartDCCMClear)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_StartDCCMClear


class ral_reg_DWC_DDRPHYA_DRTUB0_DCCMClearRunning extends uvm_reg;
	uvm_reg_field DCCMClearRunning;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DCCMClearRunning: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_DCCMClearRunning");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DCCMClearRunning = uvm_reg_field::type_id::create("DCCMClearRunning",,get_full_name());
      this.DCCMClearRunning.configure(this, 1, 0, "RO", 1, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_DCCMClearRunning)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_DCCMClearRunning


class ral_reg_DWC_DDRPHYA_DRTUB0_PIEMicroReset extends uvm_reg;
	rand uvm_reg_field PIEStallToMicro;
	rand uvm_reg_field PIEMicroResetReserved;
	rand uvm_reg_field PIEResetToMicro;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PIEStallToMicro: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PIEMicroResetReserved: coverpoint {m_data[2:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {3'b?00};
	      wildcard bins bit_0_wr_as_1 = {3'b?10};
	      wildcard bins bit_0_rd_as_0 = {3'b?01};
	      wildcard bins bit_0_rd_as_1 = {3'b?11};
	      wildcard bins bit_1_wr_as_0 = {3'b0?0};
	      wildcard bins bit_1_wr_as_1 = {3'b1?0};
	      wildcard bins bit_1_rd_as_0 = {3'b0?1};
	      wildcard bins bit_1_rd_as_1 = {3'b1?1};
	      option.weight = 8;
	   }
	   PIEResetToMicro: coverpoint {m_data[3:3], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_PIEMicroReset");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PIEStallToMicro = uvm_reg_field::type_id::create("PIEStallToMicro",,get_full_name());
      this.PIEStallToMicro.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.PIEMicroResetReserved = uvm_reg_field::type_id::create("PIEMicroResetReserved",,get_full_name());
      this.PIEMicroResetReserved.configure(this, 2, 1, "RW", 0, 2'h0, 1, 0, 0);
      this.PIEResetToMicro = uvm_reg_field::type_id::create("PIEResetToMicro",,get_full_name());
      this.PIEResetToMicro.configure(this, 1, 3, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_PIEMicroReset)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_PIEMicroReset


class ral_reg_DWC_DDRPHYA_DRTUB0_CUSTPHYREV extends uvm_reg;
	uvm_reg_field CUSTPHYREV;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CUSTPHYREV: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {7'b?????00};
	      wildcard bins bit_0_wr_as_1 = {7'b?????10};
	      wildcard bins bit_0_rd = {7'b??????1};
	      wildcard bins bit_1_wr_as_0 = {7'b????0?0};
	      wildcard bins bit_1_wr_as_1 = {7'b????1?0};
	      wildcard bins bit_1_rd = {7'b??????1};
	      wildcard bins bit_2_wr_as_0 = {7'b???0??0};
	      wildcard bins bit_2_wr_as_1 = {7'b???1??0};
	      wildcard bins bit_2_rd = {7'b??????1};
	      wildcard bins bit_3_wr_as_0 = {7'b??0???0};
	      wildcard bins bit_3_wr_as_1 = {7'b??1???0};
	      wildcard bins bit_3_rd = {7'b??????1};
	      wildcard bins bit_4_wr_as_0 = {7'b?0????0};
	      wildcard bins bit_4_wr_as_1 = {7'b?1????0};
	      wildcard bins bit_4_rd = {7'b??????1};
	      wildcard bins bit_5_wr_as_0 = {7'b0?????0};
	      wildcard bins bit_5_wr_as_1 = {7'b1?????0};
	      wildcard bins bit_5_rd = {7'b??????1};
	      option.weight = 18;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_CUSTPHYREV");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CUSTPHYREV = uvm_reg_field::type_id::create("CUSTPHYREV",,get_full_name());
      this.CUSTPHYREV.configure(this, 6, 0, "RO", 1, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_CUSTPHYREV)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_CUSTPHYREV


class ral_reg_DWC_DDRPHYA_DRTUB0_CUSTPUBREV extends uvm_reg;
	uvm_reg_field CUSTPUBREV;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CUSTPUBREV: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {7'b?????00};
	      wildcard bins bit_0_wr_as_1 = {7'b?????10};
	      wildcard bins bit_0_rd = {7'b??????1};
	      wildcard bins bit_1_wr_as_0 = {7'b????0?0};
	      wildcard bins bit_1_wr_as_1 = {7'b????1?0};
	      wildcard bins bit_1_rd = {7'b??????1};
	      wildcard bins bit_2_wr_as_0 = {7'b???0??0};
	      wildcard bins bit_2_wr_as_1 = {7'b???1??0};
	      wildcard bins bit_2_rd = {7'b??????1};
	      wildcard bins bit_3_wr_as_0 = {7'b??0???0};
	      wildcard bins bit_3_wr_as_1 = {7'b??1???0};
	      wildcard bins bit_3_rd = {7'b??????1};
	      wildcard bins bit_4_wr_as_0 = {7'b?0????0};
	      wildcard bins bit_4_wr_as_1 = {7'b?1????0};
	      wildcard bins bit_4_rd = {7'b??????1};
	      wildcard bins bit_5_wr_as_0 = {7'b0?????0};
	      wildcard bins bit_5_wr_as_1 = {7'b1?????0};
	      wildcard bins bit_5_rd = {7'b??????1};
	      option.weight = 18;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_CUSTPUBREV");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CUSTPUBREV = uvm_reg_field::type_id::create("CUSTPUBREV",,get_full_name());
      this.CUSTPUBREV.configure(this, 6, 0, "RO", 1, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_CUSTPUBREV)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_CUSTPUBREV


class ral_reg_DWC_DDRPHYA_DRTUB0_PUBREV extends uvm_reg;
	uvm_reg_field PUBMNR;
	uvm_reg_field PUBMDR;
	uvm_reg_field PUBMJR;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PUBMNR: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {5'b???00};
	      wildcard bins bit_0_wr_as_1 = {5'b???10};
	      wildcard bins bit_0_rd = {5'b????1};
	      wildcard bins bit_1_wr_as_0 = {5'b??0?0};
	      wildcard bins bit_1_wr_as_1 = {5'b??1?0};
	      wildcard bins bit_1_rd = {5'b????1};
	      wildcard bins bit_2_wr_as_0 = {5'b?0??0};
	      wildcard bins bit_2_wr_as_1 = {5'b?1??0};
	      wildcard bins bit_2_rd = {5'b????1};
	      wildcard bins bit_3_wr_as_0 = {5'b0???0};
	      wildcard bins bit_3_wr_as_1 = {5'b1???0};
	      wildcard bins bit_3_rd = {5'b????1};
	      option.weight = 12;
	   }
	   PUBMDR: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {5'b???00};
	      wildcard bins bit_0_wr_as_1 = {5'b???10};
	      wildcard bins bit_0_rd = {5'b????1};
	      wildcard bins bit_1_wr_as_0 = {5'b??0?0};
	      wildcard bins bit_1_wr_as_1 = {5'b??1?0};
	      wildcard bins bit_1_rd = {5'b????1};
	      wildcard bins bit_2_wr_as_0 = {5'b?0??0};
	      wildcard bins bit_2_wr_as_1 = {5'b?1??0};
	      wildcard bins bit_2_rd = {5'b????1};
	      wildcard bins bit_3_wr_as_0 = {5'b0???0};
	      wildcard bins bit_3_wr_as_1 = {5'b1???0};
	      wildcard bins bit_3_rd = {5'b????1};
	      option.weight = 12;
	   }
	   PUBMJR: coverpoint {m_data[15:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {9'b???????00};
	      wildcard bins bit_0_wr_as_1 = {9'b???????10};
	      wildcard bins bit_0_rd = {9'b????????1};
	      wildcard bins bit_1_wr_as_0 = {9'b??????0?0};
	      wildcard bins bit_1_wr_as_1 = {9'b??????1?0};
	      wildcard bins bit_1_rd = {9'b????????1};
	      wildcard bins bit_2_wr_as_0 = {9'b?????0??0};
	      wildcard bins bit_2_wr_as_1 = {9'b?????1??0};
	      wildcard bins bit_2_rd = {9'b????????1};
	      wildcard bins bit_3_wr_as_0 = {9'b????0???0};
	      wildcard bins bit_3_wr_as_1 = {9'b????1???0};
	      wildcard bins bit_3_rd = {9'b????????1};
	      wildcard bins bit_4_wr_as_0 = {9'b???0????0};
	      wildcard bins bit_4_wr_as_1 = {9'b???1????0};
	      wildcard bins bit_4_rd = {9'b????????1};
	      wildcard bins bit_5_wr_as_0 = {9'b??0?????0};
	      wildcard bins bit_5_wr_as_1 = {9'b??1?????0};
	      wildcard bins bit_5_rd = {9'b????????1};
	      wildcard bins bit_6_wr_as_0 = {9'b?0??????0};
	      wildcard bins bit_6_wr_as_1 = {9'b?1??????0};
	      wildcard bins bit_6_rd = {9'b????????1};
	      wildcard bins bit_7_wr_as_0 = {9'b0???????0};
	      wildcard bins bit_7_wr_as_1 = {9'b1???????0};
	      wildcard bins bit_7_rd = {9'b????????1};
	      option.weight = 24;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_PUBREV");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PUBMNR = uvm_reg_field::type_id::create("PUBMNR",,get_full_name());
      this.PUBMNR.configure(this, 4, 0, "RO", 1, 4'h0, 1, 0, 0);
      this.PUBMDR = uvm_reg_field::type_id::create("PUBMDR",,get_full_name());
      this.PUBMDR.configure(this, 4, 4, "RO", 1, 4'h0, 1, 0, 0);
      this.PUBMJR = uvm_reg_field::type_id::create("PUBMJR",,get_full_name());
      this.PUBMJR.configure(this, 8, 8, "RO", 1, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_PUBREV)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_PUBREV


class ral_reg_DWC_DDRPHYA_DRTUB0_PUBVAR extends uvm_reg;
	uvm_reg_field PUBVAR;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PUBVAR: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {17'b???????????????00};
	      wildcard bins bit_0_wr_as_1 = {17'b???????????????10};
	      wildcard bins bit_0_rd = {17'b????????????????1};
	      wildcard bins bit_1_wr_as_0 = {17'b??????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {17'b??????????????1?0};
	      wildcard bins bit_1_rd = {17'b????????????????1};
	      wildcard bins bit_2_wr_as_0 = {17'b?????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {17'b?????????????1??0};
	      wildcard bins bit_2_rd = {17'b????????????????1};
	      wildcard bins bit_3_wr_as_0 = {17'b????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {17'b????????????1???0};
	      wildcard bins bit_3_rd = {17'b????????????????1};
	      wildcard bins bit_4_wr_as_0 = {17'b???????????0????0};
	      wildcard bins bit_4_wr_as_1 = {17'b???????????1????0};
	      wildcard bins bit_4_rd = {17'b????????????????1};
	      wildcard bins bit_5_wr_as_0 = {17'b??????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {17'b??????????1?????0};
	      wildcard bins bit_5_rd = {17'b????????????????1};
	      wildcard bins bit_6_wr_as_0 = {17'b?????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {17'b?????????1??????0};
	      wildcard bins bit_6_rd = {17'b????????????????1};
	      wildcard bins bit_7_wr_as_0 = {17'b????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {17'b????????1???????0};
	      wildcard bins bit_7_rd = {17'b????????????????1};
	      wildcard bins bit_8_wr_as_0 = {17'b???????0????????0};
	      wildcard bins bit_8_wr_as_1 = {17'b???????1????????0};
	      wildcard bins bit_8_rd = {17'b????????????????1};
	      wildcard bins bit_9_wr_as_0 = {17'b??????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {17'b??????1?????????0};
	      wildcard bins bit_9_rd = {17'b????????????????1};
	      wildcard bins bit_10_wr_as_0 = {17'b?????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {17'b?????1??????????0};
	      wildcard bins bit_10_rd = {17'b????????????????1};
	      wildcard bins bit_11_wr_as_0 = {17'b????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {17'b????1???????????0};
	      wildcard bins bit_11_rd = {17'b????????????????1};
	      wildcard bins bit_12_wr_as_0 = {17'b???0????????????0};
	      wildcard bins bit_12_wr_as_1 = {17'b???1????????????0};
	      wildcard bins bit_12_rd = {17'b????????????????1};
	      wildcard bins bit_13_wr_as_0 = {17'b??0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {17'b??1?????????????0};
	      wildcard bins bit_13_rd = {17'b????????????????1};
	      wildcard bins bit_14_wr_as_0 = {17'b?0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {17'b?1??????????????0};
	      wildcard bins bit_14_rd = {17'b????????????????1};
	      wildcard bins bit_15_wr_as_0 = {17'b0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {17'b1???????????????0};
	      wildcard bins bit_15_rd = {17'b????????????????1};
	      option.weight = 48;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0_PUBVAR");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PUBVAR = uvm_reg_field::type_id::create("PUBVAR",,get_full_name());
      this.PUBVAR.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_PUBVAR)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_PUBVAR


class ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat0 extends uvm_reg;
	rand uvm_reg_field DfiFreqXlatVal0;
	rand uvm_reg_field DfiFreqXlatVal1;
	rand uvm_reg_field DfiFreqXlatVal2;
	rand uvm_reg_field DfiFreqXlatVal3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiFreqXlatVal0: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal1: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal2: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal3: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_DRTUB0_DfiFreqXlat0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiFreqXlatVal0 = uvm_reg_field::type_id::create("DfiFreqXlatVal0",,get_full_name());
      this.DfiFreqXlatVal0.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal1 = uvm_reg_field::type_id::create("DfiFreqXlatVal1",,get_full_name());
      this.DfiFreqXlatVal1.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal2 = uvm_reg_field::type_id::create("DfiFreqXlatVal2",,get_full_name());
      this.DfiFreqXlatVal2.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal3 = uvm_reg_field::type_id::create("DfiFreqXlatVal3",,get_full_name());
      this.DfiFreqXlatVal3.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat0)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat0


class ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat1 extends uvm_reg;
	rand uvm_reg_field DfiFreqXlatVal4;
	rand uvm_reg_field DfiFreqXlatVal5;
	rand uvm_reg_field DfiFreqXlatVal6;
	rand uvm_reg_field DfiFreqXlatVal7;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiFreqXlatVal4: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal5: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal6: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal7: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_DRTUB0_DfiFreqXlat1");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiFreqXlatVal4 = uvm_reg_field::type_id::create("DfiFreqXlatVal4",,get_full_name());
      this.DfiFreqXlatVal4.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal5 = uvm_reg_field::type_id::create("DfiFreqXlatVal5",,get_full_name());
      this.DfiFreqXlatVal5.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal6 = uvm_reg_field::type_id::create("DfiFreqXlatVal6",,get_full_name());
      this.DfiFreqXlatVal6.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal7 = uvm_reg_field::type_id::create("DfiFreqXlatVal7",,get_full_name());
      this.DfiFreqXlatVal7.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat1)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat1


class ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat2 extends uvm_reg;
	rand uvm_reg_field DfiFreqXlatVal8;
	rand uvm_reg_field DfiFreqXlatVal9;
	rand uvm_reg_field DfiFreqXlatVal10;
	rand uvm_reg_field DfiFreqXlatVal11;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiFreqXlatVal8: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal9: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal10: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal11: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_DRTUB0_DfiFreqXlat2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiFreqXlatVal8 = uvm_reg_field::type_id::create("DfiFreqXlatVal8",,get_full_name());
      this.DfiFreqXlatVal8.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal9 = uvm_reg_field::type_id::create("DfiFreqXlatVal9",,get_full_name());
      this.DfiFreqXlatVal9.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal10 = uvm_reg_field::type_id::create("DfiFreqXlatVal10",,get_full_name());
      this.DfiFreqXlatVal10.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal11 = uvm_reg_field::type_id::create("DfiFreqXlatVal11",,get_full_name());
      this.DfiFreqXlatVal11.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat2)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat2


class ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat3 extends uvm_reg;
	rand uvm_reg_field DfiFreqXlatVal12;
	rand uvm_reg_field DfiFreqXlatVal13;
	rand uvm_reg_field DfiFreqXlatVal14;
	rand uvm_reg_field DfiFreqXlatVal15;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiFreqXlatVal12: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal13: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal14: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal15: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_DRTUB0_DfiFreqXlat3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiFreqXlatVal12 = uvm_reg_field::type_id::create("DfiFreqXlatVal12",,get_full_name());
      this.DfiFreqXlatVal12.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal13 = uvm_reg_field::type_id::create("DfiFreqXlatVal13",,get_full_name());
      this.DfiFreqXlatVal13.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal14 = uvm_reg_field::type_id::create("DfiFreqXlatVal14",,get_full_name());
      this.DfiFreqXlatVal14.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal15 = uvm_reg_field::type_id::create("DfiFreqXlatVal15",,get_full_name());
      this.DfiFreqXlatVal15.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat3)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat3


class ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat4 extends uvm_reg;
	rand uvm_reg_field DfiFreqXlatVal16;
	rand uvm_reg_field DfiFreqXlatVal17;
	rand uvm_reg_field DfiFreqXlatVal18;
	rand uvm_reg_field DfiFreqXlatVal19;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiFreqXlatVal16: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal17: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal18: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal19: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_DRTUB0_DfiFreqXlat4");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiFreqXlatVal16 = uvm_reg_field::type_id::create("DfiFreqXlatVal16",,get_full_name());
      this.DfiFreqXlatVal16.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal17 = uvm_reg_field::type_id::create("DfiFreqXlatVal17",,get_full_name());
      this.DfiFreqXlatVal17.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal18 = uvm_reg_field::type_id::create("DfiFreqXlatVal18",,get_full_name());
      this.DfiFreqXlatVal18.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal19 = uvm_reg_field::type_id::create("DfiFreqXlatVal19",,get_full_name());
      this.DfiFreqXlatVal19.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat4)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat4


class ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat5 extends uvm_reg;
	rand uvm_reg_field DfiFreqXlatVal20;
	rand uvm_reg_field DfiFreqXlatVal21;
	rand uvm_reg_field DfiFreqXlatVal22;
	rand uvm_reg_field DfiFreqXlatVal23;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiFreqXlatVal20: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal21: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal22: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal23: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_DRTUB0_DfiFreqXlat5");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiFreqXlatVal20 = uvm_reg_field::type_id::create("DfiFreqXlatVal20",,get_full_name());
      this.DfiFreqXlatVal20.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal21 = uvm_reg_field::type_id::create("DfiFreqXlatVal21",,get_full_name());
      this.DfiFreqXlatVal21.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal22 = uvm_reg_field::type_id::create("DfiFreqXlatVal22",,get_full_name());
      this.DfiFreqXlatVal22.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal23 = uvm_reg_field::type_id::create("DfiFreqXlatVal23",,get_full_name());
      this.DfiFreqXlatVal23.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat5)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat5


class ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat6 extends uvm_reg;
	rand uvm_reg_field DfiFreqXlatVal24;
	rand uvm_reg_field DfiFreqXlatVal25;
	rand uvm_reg_field DfiFreqXlatVal26;
	rand uvm_reg_field DfiFreqXlatVal27;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiFreqXlatVal24: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal25: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal26: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal27: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_DRTUB0_DfiFreqXlat6");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiFreqXlatVal24 = uvm_reg_field::type_id::create("DfiFreqXlatVal24",,get_full_name());
      this.DfiFreqXlatVal24.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal25 = uvm_reg_field::type_id::create("DfiFreqXlatVal25",,get_full_name());
      this.DfiFreqXlatVal25.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal26 = uvm_reg_field::type_id::create("DfiFreqXlatVal26",,get_full_name());
      this.DfiFreqXlatVal26.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal27 = uvm_reg_field::type_id::create("DfiFreqXlatVal27",,get_full_name());
      this.DfiFreqXlatVal27.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat6)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat6


class ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat7 extends uvm_reg;
	rand uvm_reg_field DfiFreqXlatVal28;
	rand uvm_reg_field DfiFreqXlatVal29;
	rand uvm_reg_field DfiFreqXlatVal30;
	rand uvm_reg_field DfiFreqXlatVal31;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiFreqXlatVal28: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal29: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal30: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal31: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_DRTUB0_DfiFreqXlat7");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiFreqXlatVal28 = uvm_reg_field::type_id::create("DfiFreqXlatVal28",,get_full_name());
      this.DfiFreqXlatVal28.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal29 = uvm_reg_field::type_id::create("DfiFreqXlatVal29",,get_full_name());
      this.DfiFreqXlatVal29.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal30 = uvm_reg_field::type_id::create("DfiFreqXlatVal30",,get_full_name());
      this.DfiFreqXlatVal30.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal31 = uvm_reg_field::type_id::create("DfiFreqXlatVal31",,get_full_name());
      this.DfiFreqXlatVal31.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat7)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat7


class ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat8 extends uvm_reg;
	rand uvm_reg_field DfiFreqXlatVal32;
	rand uvm_reg_field DfiFreqXlatVal33;
	rand uvm_reg_field DfiFreqXlatVal34;
	rand uvm_reg_field DfiFreqXlatVal35;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiFreqXlatVal32: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal33: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal34: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal35: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_DRTUB0_DfiFreqXlat8");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiFreqXlatVal32 = uvm_reg_field::type_id::create("DfiFreqXlatVal32",,get_full_name());
      this.DfiFreqXlatVal32.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal33 = uvm_reg_field::type_id::create("DfiFreqXlatVal33",,get_full_name());
      this.DfiFreqXlatVal33.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal34 = uvm_reg_field::type_id::create("DfiFreqXlatVal34",,get_full_name());
      this.DfiFreqXlatVal34.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal35 = uvm_reg_field::type_id::create("DfiFreqXlatVal35",,get_full_name());
      this.DfiFreqXlatVal35.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat8)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat8


class ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat9 extends uvm_reg;
	rand uvm_reg_field DfiFreqXlatVal36;
	rand uvm_reg_field DfiFreqXlatVal37;
	rand uvm_reg_field DfiFreqXlatVal38;
	rand uvm_reg_field DfiFreqXlatVal39;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiFreqXlatVal36: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal37: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal38: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal39: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_DRTUB0_DfiFreqXlat9");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiFreqXlatVal36 = uvm_reg_field::type_id::create("DfiFreqXlatVal36",,get_full_name());
      this.DfiFreqXlatVal36.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal37 = uvm_reg_field::type_id::create("DfiFreqXlatVal37",,get_full_name());
      this.DfiFreqXlatVal37.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal38 = uvm_reg_field::type_id::create("DfiFreqXlatVal38",,get_full_name());
      this.DfiFreqXlatVal38.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal39 = uvm_reg_field::type_id::create("DfiFreqXlatVal39",,get_full_name());
      this.DfiFreqXlatVal39.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat9)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat9


class ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat10 extends uvm_reg;
	rand uvm_reg_field DfiFreqXlatVal40;
	rand uvm_reg_field DfiFreqXlatVal41;
	rand uvm_reg_field DfiFreqXlatVal42;
	rand uvm_reg_field DfiFreqXlatVal43;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiFreqXlatVal40: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal41: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal42: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal43: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_DRTUB0_DfiFreqXlat10");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiFreqXlatVal40 = uvm_reg_field::type_id::create("DfiFreqXlatVal40",,get_full_name());
      this.DfiFreqXlatVal40.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal41 = uvm_reg_field::type_id::create("DfiFreqXlatVal41",,get_full_name());
      this.DfiFreqXlatVal41.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal42 = uvm_reg_field::type_id::create("DfiFreqXlatVal42",,get_full_name());
      this.DfiFreqXlatVal42.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal43 = uvm_reg_field::type_id::create("DfiFreqXlatVal43",,get_full_name());
      this.DfiFreqXlatVal43.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat10)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat10


class ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat11 extends uvm_reg;
	rand uvm_reg_field DfiFreqXlatVal44;
	rand uvm_reg_field DfiFreqXlatVal45;
	rand uvm_reg_field DfiFreqXlatVal46;
	rand uvm_reg_field DfiFreqXlatVal47;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiFreqXlatVal44: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal45: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal46: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal47: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_DRTUB0_DfiFreqXlat11");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiFreqXlatVal44 = uvm_reg_field::type_id::create("DfiFreqXlatVal44",,get_full_name());
      this.DfiFreqXlatVal44.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal45 = uvm_reg_field::type_id::create("DfiFreqXlatVal45",,get_full_name());
      this.DfiFreqXlatVal45.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal46 = uvm_reg_field::type_id::create("DfiFreqXlatVal46",,get_full_name());
      this.DfiFreqXlatVal46.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal47 = uvm_reg_field::type_id::create("DfiFreqXlatVal47",,get_full_name());
      this.DfiFreqXlatVal47.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat11)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat11


class ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat12 extends uvm_reg;
	rand uvm_reg_field DfiFreqXlatVal48;
	rand uvm_reg_field DfiFreqXlatVal49;
	rand uvm_reg_field DfiFreqXlatVal50;
	rand uvm_reg_field DfiFreqXlatVal51;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiFreqXlatVal48: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal49: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal50: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal51: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_DRTUB0_DfiFreqXlat12");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiFreqXlatVal48 = uvm_reg_field::type_id::create("DfiFreqXlatVal48",,get_full_name());
      this.DfiFreqXlatVal48.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal49 = uvm_reg_field::type_id::create("DfiFreqXlatVal49",,get_full_name());
      this.DfiFreqXlatVal49.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal50 = uvm_reg_field::type_id::create("DfiFreqXlatVal50",,get_full_name());
      this.DfiFreqXlatVal50.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal51 = uvm_reg_field::type_id::create("DfiFreqXlatVal51",,get_full_name());
      this.DfiFreqXlatVal51.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat12)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat12


class ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat13 extends uvm_reg;
	rand uvm_reg_field DfiFreqXlatVal52;
	rand uvm_reg_field DfiFreqXlatVal53;
	rand uvm_reg_field DfiFreqXlatVal54;
	rand uvm_reg_field DfiFreqXlatVal55;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiFreqXlatVal52: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal53: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal54: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal55: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_DRTUB0_DfiFreqXlat13");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiFreqXlatVal52 = uvm_reg_field::type_id::create("DfiFreqXlatVal52",,get_full_name());
      this.DfiFreqXlatVal52.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal53 = uvm_reg_field::type_id::create("DfiFreqXlatVal53",,get_full_name());
      this.DfiFreqXlatVal53.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal54 = uvm_reg_field::type_id::create("DfiFreqXlatVal54",,get_full_name());
      this.DfiFreqXlatVal54.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal55 = uvm_reg_field::type_id::create("DfiFreqXlatVal55",,get_full_name());
      this.DfiFreqXlatVal55.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat13)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat13


class ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat14 extends uvm_reg;
	rand uvm_reg_field DfiFreqXlatVal56;
	rand uvm_reg_field DfiFreqXlatVal57;
	rand uvm_reg_field DfiFreqXlatVal58;
	rand uvm_reg_field DfiFreqXlatVal59;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiFreqXlatVal56: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal57: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal58: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal59: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_DRTUB0_DfiFreqXlat14");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiFreqXlatVal56 = uvm_reg_field::type_id::create("DfiFreqXlatVal56",,get_full_name());
      this.DfiFreqXlatVal56.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal57 = uvm_reg_field::type_id::create("DfiFreqXlatVal57",,get_full_name());
      this.DfiFreqXlatVal57.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal58 = uvm_reg_field::type_id::create("DfiFreqXlatVal58",,get_full_name());
      this.DfiFreqXlatVal58.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal59 = uvm_reg_field::type_id::create("DfiFreqXlatVal59",,get_full_name());
      this.DfiFreqXlatVal59.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat14)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat14


class ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat15 extends uvm_reg;
	rand uvm_reg_field DfiFreqXlatVal60;
	rand uvm_reg_field DfiFreqXlatVal61;
	rand uvm_reg_field DfiFreqXlatVal62;
	rand uvm_reg_field DfiFreqXlatVal63;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiFreqXlatVal60: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal61: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal62: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   DfiFreqXlatVal63: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_DRTUB0_DfiFreqXlat15");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiFreqXlatVal60 = uvm_reg_field::type_id::create("DfiFreqXlatVal60",,get_full_name());
      this.DfiFreqXlatVal60.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal61 = uvm_reg_field::type_id::create("DfiFreqXlatVal61",,get_full_name());
      this.DfiFreqXlatVal61.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal62 = uvm_reg_field::type_id::create("DfiFreqXlatVal62",,get_full_name());
      this.DfiFreqXlatVal62.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.DfiFreqXlatVal63 = uvm_reg_field::type_id::create("DfiFreqXlatVal63",,get_full_name());
      this.DfiFreqXlatVal63.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat15)

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
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat15


class ral_block_DWC_DDRPHYA_DRTUB0 extends uvm_reg_block;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_PieVecCfg PieVecCfg;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_PieInitVecSel PieInitVecSel;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_DctShadowRegs DctShadowRegs;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_DctWriteOnlyShadow DctWriteOnlyShadow;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_UctWriteOnly UctWriteOnly;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_UctWriteProt UctWriteProt;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_UctDatWriteOnly UctDatWriteOnly;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_UctDatWriteProt UctDatWriteProt;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_UctlErr UctlErr;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_DRTUBParityInvert DRTUBParityInvert;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_UCParityInvert UCParityInvert;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_ScratchPadDRTUB ScratchPadDRTUB;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_UcclkHclkEnables UcclkHclkEnables;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_ArcEccIndications ArcEccIndications;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_ArcIccmSbErrCtr ArcIccmSbErrCtr;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_ArcDccmSbErrCtr ArcDccmSbErrCtr;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_ArcSbCtrEnables ArcSbCtrEnables;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_ArcPmuEccCtl ArcPmuEccCtl;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_StartDCCMClear StartDCCMClear;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_DCCMClearRunning DCCMClearRunning;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_PIEMicroReset PIEMicroReset;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_CUSTPHYREV CUSTPHYREV;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_CUSTPUBREV CUSTPUBREV;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_PUBREV PUBREV;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_PUBVAR PUBVAR;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat0 DfiFreqXlat0;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat1 DfiFreqXlat1;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat2 DfiFreqXlat2;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat3 DfiFreqXlat3;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat4 DfiFreqXlat4;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat5 DfiFreqXlat5;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat6 DfiFreqXlat6;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat7 DfiFreqXlat7;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat8 DfiFreqXlat8;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat9 DfiFreqXlat9;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat10 DfiFreqXlat10;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat11 DfiFreqXlat11;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat12 DfiFreqXlat12;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat13 DfiFreqXlat13;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat14 DfiFreqXlat14;
	rand ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat15 DfiFreqXlat15;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field PieVecCfg_PieInitStartVec0;
	rand uvm_reg_field PieInitStartVec0;
	rand uvm_reg_field PieVecCfg_PieInitStartVec1;
	rand uvm_reg_field PieInitStartVec1;
	rand uvm_reg_field PieVecCfg_PieInitStartVec2;
	rand uvm_reg_field PieInitStartVec2;
	rand uvm_reg_field PieVecCfg_PieInitStartVec3;
	rand uvm_reg_field PieInitStartVec3;
	rand uvm_reg_field PieInitVecSel_PieInitVecSel0;
	rand uvm_reg_field PieInitVecSel0;
	rand uvm_reg_field PieInitVecSel_PieInitVecSel1;
	rand uvm_reg_field PieInitVecSel1;
	rand uvm_reg_field PieInitVecSel_PieInitVecSel2;
	rand uvm_reg_field PieInitVecSel2;
	rand uvm_reg_field PieInitVecSel_PieInitVecSel3;
	rand uvm_reg_field PieInitVecSel3;
	uvm_reg_field DctShadowRegs_DctShadowRegs;
	uvm_reg_field DctWriteOnlyShadow_DctWriteOnlyShadow;
	rand uvm_reg_field UctWriteOnly_UctWriteOnly;
	rand uvm_reg_field UctWriteProt_UctWriteProt;
	rand uvm_reg_field UctDatWriteOnly_UctDatWriteOnly;
	rand uvm_reg_field UctDatWriteProt_UctDatWriteProt;
	rand uvm_reg_field UctlErr_UctlErr;
	rand uvm_reg_field DRTUBParityInvert_DRTUBParityInvert;
	rand uvm_reg_field UCParityInvert_UCParityInvert;
	rand uvm_reg_field ScratchPadDRTUB_ScratchPadDRTUB;
	rand uvm_reg_field UcclkHclkEnables_UcclkEn;
	rand uvm_reg_field UcclkEn;
	rand uvm_reg_field UcclkHclkEnables_HclkEn;
	rand uvm_reg_field HclkEn;
	rand uvm_reg_field UcclkHclkEnables_UcclkFull;
	rand uvm_reg_field UcclkFull;
	uvm_reg_field ArcEccIndications_ArcDccmDbError;
	uvm_reg_field ArcDccmDbError;
	uvm_reg_field ArcEccIndications_ArcIccmDbError;
	uvm_reg_field ArcIccmDbError;
	uvm_reg_field ArcIccmSbErrCtr_ArcIccmSbErrCtr;
	uvm_reg_field ArcDccmSbErrCtr_ArcDccmSbErrCtr;
	rand uvm_reg_field ArcSbCtrEnables_ArcIccmSbCtrEn;
	rand uvm_reg_field ArcIccmSbCtrEn;
	rand uvm_reg_field ArcSbCtrEnables_ArcDccmSbCtrEn;
	rand uvm_reg_field ArcDccmSbCtrEn;
	rand uvm_reg_field ArcPmuEccCtl_ArcPmuEccCtl;
	rand uvm_reg_field StartDCCMClear_StartDCCMClear;
	uvm_reg_field DCCMClearRunning_DCCMClearRunning;
	rand uvm_reg_field PIEMicroReset_PIEStallToMicro;
	rand uvm_reg_field PIEStallToMicro;
	rand uvm_reg_field PIEMicroReset_PIEMicroResetReserved;
	rand uvm_reg_field PIEMicroResetReserved;
	rand uvm_reg_field PIEMicroReset_PIEResetToMicro;
	rand uvm_reg_field PIEResetToMicro;
	uvm_reg_field CUSTPHYREV_CUSTPHYREV;
	uvm_reg_field CUSTPUBREV_CUSTPUBREV;
	uvm_reg_field PUBREV_PUBMNR;
	uvm_reg_field PUBMNR;
	uvm_reg_field PUBREV_PUBMDR;
	uvm_reg_field PUBMDR;
	uvm_reg_field PUBREV_PUBMJR;
	uvm_reg_field PUBMJR;
	uvm_reg_field PUBVAR_PUBVAR;
	rand uvm_reg_field DfiFreqXlat0_DfiFreqXlatVal0;
	rand uvm_reg_field DfiFreqXlatVal0;
	rand uvm_reg_field DfiFreqXlat0_DfiFreqXlatVal1;
	rand uvm_reg_field DfiFreqXlatVal1;
	rand uvm_reg_field DfiFreqXlat0_DfiFreqXlatVal2;
	rand uvm_reg_field DfiFreqXlatVal2;
	rand uvm_reg_field DfiFreqXlat0_DfiFreqXlatVal3;
	rand uvm_reg_field DfiFreqXlatVal3;
	rand uvm_reg_field DfiFreqXlat1_DfiFreqXlatVal4;
	rand uvm_reg_field DfiFreqXlatVal4;
	rand uvm_reg_field DfiFreqXlat1_DfiFreqXlatVal5;
	rand uvm_reg_field DfiFreqXlatVal5;
	rand uvm_reg_field DfiFreqXlat1_DfiFreqXlatVal6;
	rand uvm_reg_field DfiFreqXlatVal6;
	rand uvm_reg_field DfiFreqXlat1_DfiFreqXlatVal7;
	rand uvm_reg_field DfiFreqXlatVal7;
	rand uvm_reg_field DfiFreqXlat2_DfiFreqXlatVal8;
	rand uvm_reg_field DfiFreqXlatVal8;
	rand uvm_reg_field DfiFreqXlat2_DfiFreqXlatVal9;
	rand uvm_reg_field DfiFreqXlatVal9;
	rand uvm_reg_field DfiFreqXlat2_DfiFreqXlatVal10;
	rand uvm_reg_field DfiFreqXlatVal10;
	rand uvm_reg_field DfiFreqXlat2_DfiFreqXlatVal11;
	rand uvm_reg_field DfiFreqXlatVal11;
	rand uvm_reg_field DfiFreqXlat3_DfiFreqXlatVal12;
	rand uvm_reg_field DfiFreqXlatVal12;
	rand uvm_reg_field DfiFreqXlat3_DfiFreqXlatVal13;
	rand uvm_reg_field DfiFreqXlatVal13;
	rand uvm_reg_field DfiFreqXlat3_DfiFreqXlatVal14;
	rand uvm_reg_field DfiFreqXlatVal14;
	rand uvm_reg_field DfiFreqXlat3_DfiFreqXlatVal15;
	rand uvm_reg_field DfiFreqXlatVal15;
	rand uvm_reg_field DfiFreqXlat4_DfiFreqXlatVal16;
	rand uvm_reg_field DfiFreqXlatVal16;
	rand uvm_reg_field DfiFreqXlat4_DfiFreqXlatVal17;
	rand uvm_reg_field DfiFreqXlatVal17;
	rand uvm_reg_field DfiFreqXlat4_DfiFreqXlatVal18;
	rand uvm_reg_field DfiFreqXlatVal18;
	rand uvm_reg_field DfiFreqXlat4_DfiFreqXlatVal19;
	rand uvm_reg_field DfiFreqXlatVal19;
	rand uvm_reg_field DfiFreqXlat5_DfiFreqXlatVal20;
	rand uvm_reg_field DfiFreqXlatVal20;
	rand uvm_reg_field DfiFreqXlat5_DfiFreqXlatVal21;
	rand uvm_reg_field DfiFreqXlatVal21;
	rand uvm_reg_field DfiFreqXlat5_DfiFreqXlatVal22;
	rand uvm_reg_field DfiFreqXlatVal22;
	rand uvm_reg_field DfiFreqXlat5_DfiFreqXlatVal23;
	rand uvm_reg_field DfiFreqXlatVal23;
	rand uvm_reg_field DfiFreqXlat6_DfiFreqXlatVal24;
	rand uvm_reg_field DfiFreqXlatVal24;
	rand uvm_reg_field DfiFreqXlat6_DfiFreqXlatVal25;
	rand uvm_reg_field DfiFreqXlatVal25;
	rand uvm_reg_field DfiFreqXlat6_DfiFreqXlatVal26;
	rand uvm_reg_field DfiFreqXlatVal26;
	rand uvm_reg_field DfiFreqXlat6_DfiFreqXlatVal27;
	rand uvm_reg_field DfiFreqXlatVal27;
	rand uvm_reg_field DfiFreqXlat7_DfiFreqXlatVal28;
	rand uvm_reg_field DfiFreqXlatVal28;
	rand uvm_reg_field DfiFreqXlat7_DfiFreqXlatVal29;
	rand uvm_reg_field DfiFreqXlatVal29;
	rand uvm_reg_field DfiFreqXlat7_DfiFreqXlatVal30;
	rand uvm_reg_field DfiFreqXlatVal30;
	rand uvm_reg_field DfiFreqXlat7_DfiFreqXlatVal31;
	rand uvm_reg_field DfiFreqXlatVal31;
	rand uvm_reg_field DfiFreqXlat8_DfiFreqXlatVal32;
	rand uvm_reg_field DfiFreqXlatVal32;
	rand uvm_reg_field DfiFreqXlat8_DfiFreqXlatVal33;
	rand uvm_reg_field DfiFreqXlatVal33;
	rand uvm_reg_field DfiFreqXlat8_DfiFreqXlatVal34;
	rand uvm_reg_field DfiFreqXlatVal34;
	rand uvm_reg_field DfiFreqXlat8_DfiFreqXlatVal35;
	rand uvm_reg_field DfiFreqXlatVal35;
	rand uvm_reg_field DfiFreqXlat9_DfiFreqXlatVal36;
	rand uvm_reg_field DfiFreqXlatVal36;
	rand uvm_reg_field DfiFreqXlat9_DfiFreqXlatVal37;
	rand uvm_reg_field DfiFreqXlatVal37;
	rand uvm_reg_field DfiFreqXlat9_DfiFreqXlatVal38;
	rand uvm_reg_field DfiFreqXlatVal38;
	rand uvm_reg_field DfiFreqXlat9_DfiFreqXlatVal39;
	rand uvm_reg_field DfiFreqXlatVal39;
	rand uvm_reg_field DfiFreqXlat10_DfiFreqXlatVal40;
	rand uvm_reg_field DfiFreqXlatVal40;
	rand uvm_reg_field DfiFreqXlat10_DfiFreqXlatVal41;
	rand uvm_reg_field DfiFreqXlatVal41;
	rand uvm_reg_field DfiFreqXlat10_DfiFreqXlatVal42;
	rand uvm_reg_field DfiFreqXlatVal42;
	rand uvm_reg_field DfiFreqXlat10_DfiFreqXlatVal43;
	rand uvm_reg_field DfiFreqXlatVal43;
	rand uvm_reg_field DfiFreqXlat11_DfiFreqXlatVal44;
	rand uvm_reg_field DfiFreqXlatVal44;
	rand uvm_reg_field DfiFreqXlat11_DfiFreqXlatVal45;
	rand uvm_reg_field DfiFreqXlatVal45;
	rand uvm_reg_field DfiFreqXlat11_DfiFreqXlatVal46;
	rand uvm_reg_field DfiFreqXlatVal46;
	rand uvm_reg_field DfiFreqXlat11_DfiFreqXlatVal47;
	rand uvm_reg_field DfiFreqXlatVal47;
	rand uvm_reg_field DfiFreqXlat12_DfiFreqXlatVal48;
	rand uvm_reg_field DfiFreqXlatVal48;
	rand uvm_reg_field DfiFreqXlat12_DfiFreqXlatVal49;
	rand uvm_reg_field DfiFreqXlatVal49;
	rand uvm_reg_field DfiFreqXlat12_DfiFreqXlatVal50;
	rand uvm_reg_field DfiFreqXlatVal50;
	rand uvm_reg_field DfiFreqXlat12_DfiFreqXlatVal51;
	rand uvm_reg_field DfiFreqXlatVal51;
	rand uvm_reg_field DfiFreqXlat13_DfiFreqXlatVal52;
	rand uvm_reg_field DfiFreqXlatVal52;
	rand uvm_reg_field DfiFreqXlat13_DfiFreqXlatVal53;
	rand uvm_reg_field DfiFreqXlatVal53;
	rand uvm_reg_field DfiFreqXlat13_DfiFreqXlatVal54;
	rand uvm_reg_field DfiFreqXlatVal54;
	rand uvm_reg_field DfiFreqXlat13_DfiFreqXlatVal55;
	rand uvm_reg_field DfiFreqXlatVal55;
	rand uvm_reg_field DfiFreqXlat14_DfiFreqXlatVal56;
	rand uvm_reg_field DfiFreqXlatVal56;
	rand uvm_reg_field DfiFreqXlat14_DfiFreqXlatVal57;
	rand uvm_reg_field DfiFreqXlatVal57;
	rand uvm_reg_field DfiFreqXlat14_DfiFreqXlatVal58;
	rand uvm_reg_field DfiFreqXlatVal58;
	rand uvm_reg_field DfiFreqXlat14_DfiFreqXlatVal59;
	rand uvm_reg_field DfiFreqXlatVal59;
	rand uvm_reg_field DfiFreqXlat15_DfiFreqXlatVal60;
	rand uvm_reg_field DfiFreqXlatVal60;
	rand uvm_reg_field DfiFreqXlat15_DfiFreqXlatVal61;
	rand uvm_reg_field DfiFreqXlatVal61;
	rand uvm_reg_field DfiFreqXlat15_DfiFreqXlatVal62;
	rand uvm_reg_field DfiFreqXlatVal62;
	rand uvm_reg_field DfiFreqXlat15_DfiFreqXlatVal63;
	rand uvm_reg_field DfiFreqXlatVal63;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	PieVecCfg : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h0 };
		option.weight = 1;
	}

	PieInitVecSel : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1 };
		option.weight = 1;
	}

	DctShadowRegs : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4 };
		option.weight = 1;
	}

	DctWriteOnlyShadow : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h30 };
		option.weight = 1;
	}

	UctWriteOnly : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h32 };
		option.weight = 1;
	}

	UctWriteProt : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h33 };
		option.weight = 1;
	}

	UctDatWriteOnly : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h34 };
		option.weight = 1;
	}

	UctDatWriteProt : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h35 };
		option.weight = 1;
	}

	UctlErr : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h36 };
		option.weight = 1;
	}

	DRTUBParityInvert : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4D };
		option.weight = 1;
	}

	UCParityInvert : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4E };
		option.weight = 1;
	}

	ScratchPadDRTUB : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h7D };
		option.weight = 1;
	}

	UcclkHclkEnables : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h80 };
		option.weight = 1;
	}

	ArcEccIndications : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h82 };
		option.weight = 1;
	}

	ArcIccmSbErrCtr : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h83 };
		option.weight = 1;
	}

	ArcDccmSbErrCtr : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h84 };
		option.weight = 1;
	}

	ArcSbCtrEnables : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h85 };
		option.weight = 1;
	}

	ArcPmuEccCtl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h86 };
		option.weight = 1;
	}

	StartDCCMClear : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h88 };
		option.weight = 1;
	}

	DCCMClearRunning : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h89 };
		option.weight = 1;
	}

	PIEMicroReset : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h99 };
		option.weight = 1;
	}

	CUSTPHYREV : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hEC };
		option.weight = 1;
	}

	CUSTPUBREV : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hED };
		option.weight = 1;
	}

	PUBREV : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hEE };
		option.weight = 1;
	}

	PUBVAR : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hEF };
		option.weight = 1;
	}

	DfiFreqXlat0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF0 };
		option.weight = 1;
	}

	DfiFreqXlat1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF1 };
		option.weight = 1;
	}

	DfiFreqXlat2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF2 };
		option.weight = 1;
	}

	DfiFreqXlat3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF3 };
		option.weight = 1;
	}

	DfiFreqXlat4 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF4 };
		option.weight = 1;
	}

	DfiFreqXlat5 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF5 };
		option.weight = 1;
	}

	DfiFreqXlat6 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF6 };
		option.weight = 1;
	}

	DfiFreqXlat7 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF7 };
		option.weight = 1;
	}

	DfiFreqXlat8 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF8 };
		option.weight = 1;
	}

	DfiFreqXlat9 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF9 };
		option.weight = 1;
	}

	DfiFreqXlat10 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFA };
		option.weight = 1;
	}

	DfiFreqXlat11 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFB };
		option.weight = 1;
	}

	DfiFreqXlat12 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFC };
		option.weight = 1;
	}

	DfiFreqXlat13 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFD };
		option.weight = 1;
	}

	DfiFreqXlat14 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFE };
		option.weight = 1;
	}

	DfiFreqXlat15 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFF };
		option.weight = 1;
	}
endgroup
	function new(string name = "DWC_DDRPHYA_DRTUB0");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.PieVecCfg = ral_reg_DWC_DDRPHYA_DRTUB0_PieVecCfg::type_id::create("PieVecCfg",,get_full_name());
      if(this.PieVecCfg.has_coverage(UVM_CVR_ALL))
      	this.PieVecCfg.cg_bits.option.name = {get_name(), ".", "PieVecCfg_bits"};
      this.PieVecCfg.configure(this, null, "");
      this.PieVecCfg.build();
      this.default_map.add_reg(this.PieVecCfg, `UVM_REG_ADDR_WIDTH'h0, "RW", 0);
		this.PieVecCfg_PieInitStartVec0 = this.PieVecCfg.PieInitStartVec0;
		this.PieInitStartVec0 = this.PieVecCfg.PieInitStartVec0;
		this.PieVecCfg_PieInitStartVec1 = this.PieVecCfg.PieInitStartVec1;
		this.PieInitStartVec1 = this.PieVecCfg.PieInitStartVec1;
		this.PieVecCfg_PieInitStartVec2 = this.PieVecCfg.PieInitStartVec2;
		this.PieInitStartVec2 = this.PieVecCfg.PieInitStartVec2;
		this.PieVecCfg_PieInitStartVec3 = this.PieVecCfg.PieInitStartVec3;
		this.PieInitStartVec3 = this.PieVecCfg.PieInitStartVec3;
      this.PieInitVecSel = ral_reg_DWC_DDRPHYA_DRTUB0_PieInitVecSel::type_id::create("PieInitVecSel",,get_full_name());
      if(this.PieInitVecSel.has_coverage(UVM_CVR_ALL))
      	this.PieInitVecSel.cg_bits.option.name = {get_name(), ".", "PieInitVecSel_bits"};
      this.PieInitVecSel.configure(this, null, "");
      this.PieInitVecSel.build();
      this.default_map.add_reg(this.PieInitVecSel, `UVM_REG_ADDR_WIDTH'h1, "RW", 0);
		this.PieInitVecSel_PieInitVecSel0 = this.PieInitVecSel.PieInitVecSel0;
		this.PieInitVecSel0 = this.PieInitVecSel.PieInitVecSel0;
		this.PieInitVecSel_PieInitVecSel1 = this.PieInitVecSel.PieInitVecSel1;
		this.PieInitVecSel1 = this.PieInitVecSel.PieInitVecSel1;
		this.PieInitVecSel_PieInitVecSel2 = this.PieInitVecSel.PieInitVecSel2;
		this.PieInitVecSel2 = this.PieInitVecSel.PieInitVecSel2;
		this.PieInitVecSel_PieInitVecSel3 = this.PieInitVecSel.PieInitVecSel3;
		this.PieInitVecSel3 = this.PieInitVecSel.PieInitVecSel3;
      this.DctShadowRegs = ral_reg_DWC_DDRPHYA_DRTUB0_DctShadowRegs::type_id::create("DctShadowRegs",,get_full_name());
      if(this.DctShadowRegs.has_coverage(UVM_CVR_ALL))
      	this.DctShadowRegs.cg_bits.option.name = {get_name(), ".", "DctShadowRegs_bits"};
      this.DctShadowRegs.configure(this, null, "");
      this.DctShadowRegs.build();
      this.default_map.add_reg(this.DctShadowRegs, `UVM_REG_ADDR_WIDTH'h4, "RO", 0);
		this.DctShadowRegs_DctShadowRegs = this.DctShadowRegs.DctShadowRegs;
      this.DctWriteOnlyShadow = ral_reg_DWC_DDRPHYA_DRTUB0_DctWriteOnlyShadow::type_id::create("DctWriteOnlyShadow",,get_full_name());
      if(this.DctWriteOnlyShadow.has_coverage(UVM_CVR_ALL))
      	this.DctWriteOnlyShadow.cg_bits.option.name = {get_name(), ".", "DctWriteOnlyShadow_bits"};
      this.DctWriteOnlyShadow.configure(this, null, "");
      this.DctWriteOnlyShadow.build();
      this.default_map.add_reg(this.DctWriteOnlyShadow, `UVM_REG_ADDR_WIDTH'h30, "RO", 0);
		this.DctWriteOnlyShadow_DctWriteOnlyShadow = this.DctWriteOnlyShadow.DctWriteOnlyShadow;
      this.UctWriteOnly = ral_reg_DWC_DDRPHYA_DRTUB0_UctWriteOnly::type_id::create("UctWriteOnly",,get_full_name());
      if(this.UctWriteOnly.has_coverage(UVM_CVR_ALL))
      	this.UctWriteOnly.cg_bits.option.name = {get_name(), ".", "UctWriteOnly_bits"};
      this.UctWriteOnly.configure(this, null, "");
      this.UctWriteOnly.build();
      this.default_map.add_reg(this.UctWriteOnly, `UVM_REG_ADDR_WIDTH'h32, "RW", 0);
		this.UctWriteOnly_UctWriteOnly = this.UctWriteOnly.UctWriteOnly;
      this.UctWriteProt = ral_reg_DWC_DDRPHYA_DRTUB0_UctWriteProt::type_id::create("UctWriteProt",,get_full_name());
      if(this.UctWriteProt.has_coverage(UVM_CVR_ALL))
      	this.UctWriteProt.cg_bits.option.name = {get_name(), ".", "UctWriteProt_bits"};
      this.UctWriteProt.configure(this, null, "");
      this.UctWriteProt.build();
      this.default_map.add_reg(this.UctWriteProt, `UVM_REG_ADDR_WIDTH'h33, "RW", 0);
		this.UctWriteProt_UctWriteProt = this.UctWriteProt.UctWriteProt;
      this.UctDatWriteOnly = ral_reg_DWC_DDRPHYA_DRTUB0_UctDatWriteOnly::type_id::create("UctDatWriteOnly",,get_full_name());
      if(this.UctDatWriteOnly.has_coverage(UVM_CVR_ALL))
      	this.UctDatWriteOnly.cg_bits.option.name = {get_name(), ".", "UctDatWriteOnly_bits"};
      this.UctDatWriteOnly.configure(this, null, "");
      this.UctDatWriteOnly.build();
      this.default_map.add_reg(this.UctDatWriteOnly, `UVM_REG_ADDR_WIDTH'h34, "RW", 0);
		this.UctDatWriteOnly_UctDatWriteOnly = this.UctDatWriteOnly.UctDatWriteOnly;
      this.UctDatWriteProt = ral_reg_DWC_DDRPHYA_DRTUB0_UctDatWriteProt::type_id::create("UctDatWriteProt",,get_full_name());
      if(this.UctDatWriteProt.has_coverage(UVM_CVR_ALL))
      	this.UctDatWriteProt.cg_bits.option.name = {get_name(), ".", "UctDatWriteProt_bits"};
      this.UctDatWriteProt.configure(this, null, "");
      this.UctDatWriteProt.build();
      this.default_map.add_reg(this.UctDatWriteProt, `UVM_REG_ADDR_WIDTH'h35, "RW", 0);
		this.UctDatWriteProt_UctDatWriteProt = this.UctDatWriteProt.UctDatWriteProt;
      this.UctlErr = ral_reg_DWC_DDRPHYA_DRTUB0_UctlErr::type_id::create("UctlErr",,get_full_name());
      if(this.UctlErr.has_coverage(UVM_CVR_ALL))
      	this.UctlErr.cg_bits.option.name = {get_name(), ".", "UctlErr_bits"};
      this.UctlErr.configure(this, null, "");
      this.UctlErr.build();
      this.default_map.add_reg(this.UctlErr, `UVM_REG_ADDR_WIDTH'h36, "RW", 0);
		this.UctlErr_UctlErr = this.UctlErr.UctlErr;
      this.DRTUBParityInvert = ral_reg_DWC_DDRPHYA_DRTUB0_DRTUBParityInvert::type_id::create("DRTUBParityInvert",,get_full_name());
      if(this.DRTUBParityInvert.has_coverage(UVM_CVR_ALL))
      	this.DRTUBParityInvert.cg_bits.option.name = {get_name(), ".", "DRTUBParityInvert_bits"};
      this.DRTUBParityInvert.configure(this, null, "");
      this.DRTUBParityInvert.build();
      this.default_map.add_reg(this.DRTUBParityInvert, `UVM_REG_ADDR_WIDTH'h4D, "RW", 0);
		this.DRTUBParityInvert_DRTUBParityInvert = this.DRTUBParityInvert.DRTUBParityInvert;
      this.UCParityInvert = ral_reg_DWC_DDRPHYA_DRTUB0_UCParityInvert::type_id::create("UCParityInvert",,get_full_name());
      if(this.UCParityInvert.has_coverage(UVM_CVR_ALL))
      	this.UCParityInvert.cg_bits.option.name = {get_name(), ".", "UCParityInvert_bits"};
      this.UCParityInvert.configure(this, null, "");
      this.UCParityInvert.build();
      this.default_map.add_reg(this.UCParityInvert, `UVM_REG_ADDR_WIDTH'h4E, "RW", 0);
		this.UCParityInvert_UCParityInvert = this.UCParityInvert.UCParityInvert;
      this.ScratchPadDRTUB = ral_reg_DWC_DDRPHYA_DRTUB0_ScratchPadDRTUB::type_id::create("ScratchPadDRTUB",,get_full_name());
      if(this.ScratchPadDRTUB.has_coverage(UVM_CVR_ALL))
      	this.ScratchPadDRTUB.cg_bits.option.name = {get_name(), ".", "ScratchPadDRTUB_bits"};
      this.ScratchPadDRTUB.configure(this, null, "");
      this.ScratchPadDRTUB.build();
      this.default_map.add_reg(this.ScratchPadDRTUB, `UVM_REG_ADDR_WIDTH'h7D, "RW", 0);
		this.ScratchPadDRTUB_ScratchPadDRTUB = this.ScratchPadDRTUB.ScratchPadDRTUB;
      this.UcclkHclkEnables = ral_reg_DWC_DDRPHYA_DRTUB0_UcclkHclkEnables::type_id::create("UcclkHclkEnables",,get_full_name());
      if(this.UcclkHclkEnables.has_coverage(UVM_CVR_ALL))
      	this.UcclkHclkEnables.cg_bits.option.name = {get_name(), ".", "UcclkHclkEnables_bits"};
      this.UcclkHclkEnables.configure(this, null, "");
      this.UcclkHclkEnables.build();
      this.default_map.add_reg(this.UcclkHclkEnables, `UVM_REG_ADDR_WIDTH'h80, "RW", 0);
		this.UcclkHclkEnables_UcclkEn = this.UcclkHclkEnables.UcclkEn;
		this.UcclkEn = this.UcclkHclkEnables.UcclkEn;
		this.UcclkHclkEnables_HclkEn = this.UcclkHclkEnables.HclkEn;
		this.HclkEn = this.UcclkHclkEnables.HclkEn;
		this.UcclkHclkEnables_UcclkFull = this.UcclkHclkEnables.UcclkFull;
		this.UcclkFull = this.UcclkHclkEnables.UcclkFull;
      this.ArcEccIndications = ral_reg_DWC_DDRPHYA_DRTUB0_ArcEccIndications::type_id::create("ArcEccIndications",,get_full_name());
      if(this.ArcEccIndications.has_coverage(UVM_CVR_ALL))
      	this.ArcEccIndications.cg_bits.option.name = {get_name(), ".", "ArcEccIndications_bits"};
      this.ArcEccIndications.configure(this, null, "");
      this.ArcEccIndications.build();
      this.default_map.add_reg(this.ArcEccIndications, `UVM_REG_ADDR_WIDTH'h82, "RO", 0);
		this.ArcEccIndications_ArcDccmDbError = this.ArcEccIndications.ArcDccmDbError;
		this.ArcDccmDbError = this.ArcEccIndications.ArcDccmDbError;
		this.ArcEccIndications_ArcIccmDbError = this.ArcEccIndications.ArcIccmDbError;
		this.ArcIccmDbError = this.ArcEccIndications.ArcIccmDbError;
      this.ArcIccmSbErrCtr = ral_reg_DWC_DDRPHYA_DRTUB0_ArcIccmSbErrCtr::type_id::create("ArcIccmSbErrCtr",,get_full_name());
      if(this.ArcIccmSbErrCtr.has_coverage(UVM_CVR_ALL))
      	this.ArcIccmSbErrCtr.cg_bits.option.name = {get_name(), ".", "ArcIccmSbErrCtr_bits"};
      this.ArcIccmSbErrCtr.configure(this, null, "");
      this.ArcIccmSbErrCtr.build();
      this.default_map.add_reg(this.ArcIccmSbErrCtr, `UVM_REG_ADDR_WIDTH'h83, "RO", 0);
		this.ArcIccmSbErrCtr_ArcIccmSbErrCtr = this.ArcIccmSbErrCtr.ArcIccmSbErrCtr;
      this.ArcDccmSbErrCtr = ral_reg_DWC_DDRPHYA_DRTUB0_ArcDccmSbErrCtr::type_id::create("ArcDccmSbErrCtr",,get_full_name());
      if(this.ArcDccmSbErrCtr.has_coverage(UVM_CVR_ALL))
      	this.ArcDccmSbErrCtr.cg_bits.option.name = {get_name(), ".", "ArcDccmSbErrCtr_bits"};
      this.ArcDccmSbErrCtr.configure(this, null, "");
      this.ArcDccmSbErrCtr.build();
      this.default_map.add_reg(this.ArcDccmSbErrCtr, `UVM_REG_ADDR_WIDTH'h84, "RO", 0);
		this.ArcDccmSbErrCtr_ArcDccmSbErrCtr = this.ArcDccmSbErrCtr.ArcDccmSbErrCtr;
      this.ArcSbCtrEnables = ral_reg_DWC_DDRPHYA_DRTUB0_ArcSbCtrEnables::type_id::create("ArcSbCtrEnables",,get_full_name());
      if(this.ArcSbCtrEnables.has_coverage(UVM_CVR_ALL))
      	this.ArcSbCtrEnables.cg_bits.option.name = {get_name(), ".", "ArcSbCtrEnables_bits"};
      this.ArcSbCtrEnables.configure(this, null, "");
      this.ArcSbCtrEnables.build();
      this.default_map.add_reg(this.ArcSbCtrEnables, `UVM_REG_ADDR_WIDTH'h85, "RW", 0);
		this.ArcSbCtrEnables_ArcIccmSbCtrEn = this.ArcSbCtrEnables.ArcIccmSbCtrEn;
		this.ArcIccmSbCtrEn = this.ArcSbCtrEnables.ArcIccmSbCtrEn;
		this.ArcSbCtrEnables_ArcDccmSbCtrEn = this.ArcSbCtrEnables.ArcDccmSbCtrEn;
		this.ArcDccmSbCtrEn = this.ArcSbCtrEnables.ArcDccmSbCtrEn;
      this.ArcPmuEccCtl = ral_reg_DWC_DDRPHYA_DRTUB0_ArcPmuEccCtl::type_id::create("ArcPmuEccCtl",,get_full_name());
      if(this.ArcPmuEccCtl.has_coverage(UVM_CVR_ALL))
      	this.ArcPmuEccCtl.cg_bits.option.name = {get_name(), ".", "ArcPmuEccCtl_bits"};
      this.ArcPmuEccCtl.configure(this, null, "");
      this.ArcPmuEccCtl.build();
      this.default_map.add_reg(this.ArcPmuEccCtl, `UVM_REG_ADDR_WIDTH'h86, "RW", 0);
		this.ArcPmuEccCtl_ArcPmuEccCtl = this.ArcPmuEccCtl.ArcPmuEccCtl;
      this.StartDCCMClear = ral_reg_DWC_DDRPHYA_DRTUB0_StartDCCMClear::type_id::create("StartDCCMClear",,get_full_name());
      if(this.StartDCCMClear.has_coverage(UVM_CVR_ALL))
      	this.StartDCCMClear.cg_bits.option.name = {get_name(), ".", "StartDCCMClear_bits"};
      this.StartDCCMClear.configure(this, null, "");
      this.StartDCCMClear.build();
      this.default_map.add_reg(this.StartDCCMClear, `UVM_REG_ADDR_WIDTH'h88, "RW", 0);
		this.StartDCCMClear_StartDCCMClear = this.StartDCCMClear.StartDCCMClear;
      this.DCCMClearRunning = ral_reg_DWC_DDRPHYA_DRTUB0_DCCMClearRunning::type_id::create("DCCMClearRunning",,get_full_name());
      if(this.DCCMClearRunning.has_coverage(UVM_CVR_ALL))
      	this.DCCMClearRunning.cg_bits.option.name = {get_name(), ".", "DCCMClearRunning_bits"};
      this.DCCMClearRunning.configure(this, null, "");
      this.DCCMClearRunning.build();
      this.default_map.add_reg(this.DCCMClearRunning, `UVM_REG_ADDR_WIDTH'h89, "RO", 0);
		this.DCCMClearRunning_DCCMClearRunning = this.DCCMClearRunning.DCCMClearRunning;
      this.PIEMicroReset = ral_reg_DWC_DDRPHYA_DRTUB0_PIEMicroReset::type_id::create("PIEMicroReset",,get_full_name());
      if(this.PIEMicroReset.has_coverage(UVM_CVR_ALL))
      	this.PIEMicroReset.cg_bits.option.name = {get_name(), ".", "PIEMicroReset_bits"};
      this.PIEMicroReset.configure(this, null, "");
      this.PIEMicroReset.build();
      this.default_map.add_reg(this.PIEMicroReset, `UVM_REG_ADDR_WIDTH'h99, "RW", 0);
		this.PIEMicroReset_PIEStallToMicro = this.PIEMicroReset.PIEStallToMicro;
		this.PIEStallToMicro = this.PIEMicroReset.PIEStallToMicro;
		this.PIEMicroReset_PIEMicroResetReserved = this.PIEMicroReset.PIEMicroResetReserved;
		this.PIEMicroResetReserved = this.PIEMicroReset.PIEMicroResetReserved;
		this.PIEMicroReset_PIEResetToMicro = this.PIEMicroReset.PIEResetToMicro;
		this.PIEResetToMicro = this.PIEMicroReset.PIEResetToMicro;
      this.CUSTPHYREV = ral_reg_DWC_DDRPHYA_DRTUB0_CUSTPHYREV::type_id::create("CUSTPHYREV",,get_full_name());
      if(this.CUSTPHYREV.has_coverage(UVM_CVR_ALL))
      	this.CUSTPHYREV.cg_bits.option.name = {get_name(), ".", "CUSTPHYREV_bits"};
      this.CUSTPHYREV.configure(this, null, "");
      this.CUSTPHYREV.build();
      this.default_map.add_reg(this.CUSTPHYREV, `UVM_REG_ADDR_WIDTH'hEC, "RO", 0);
		this.CUSTPHYREV_CUSTPHYREV = this.CUSTPHYREV.CUSTPHYREV;
      this.CUSTPUBREV = ral_reg_DWC_DDRPHYA_DRTUB0_CUSTPUBREV::type_id::create("CUSTPUBREV",,get_full_name());
      if(this.CUSTPUBREV.has_coverage(UVM_CVR_ALL))
      	this.CUSTPUBREV.cg_bits.option.name = {get_name(), ".", "CUSTPUBREV_bits"};
      this.CUSTPUBREV.configure(this, null, "");
      this.CUSTPUBREV.build();
      this.default_map.add_reg(this.CUSTPUBREV, `UVM_REG_ADDR_WIDTH'hED, "RO", 0);
		this.CUSTPUBREV_CUSTPUBREV = this.CUSTPUBREV.CUSTPUBREV;
      this.PUBREV = ral_reg_DWC_DDRPHYA_DRTUB0_PUBREV::type_id::create("PUBREV",,get_full_name());
      if(this.PUBREV.has_coverage(UVM_CVR_ALL))
      	this.PUBREV.cg_bits.option.name = {get_name(), ".", "PUBREV_bits"};
      this.PUBREV.configure(this, null, "");
      this.PUBREV.build();
      this.default_map.add_reg(this.PUBREV, `UVM_REG_ADDR_WIDTH'hEE, "RO", 0);
		this.PUBREV_PUBMNR = this.PUBREV.PUBMNR;
		this.PUBMNR = this.PUBREV.PUBMNR;
		this.PUBREV_PUBMDR = this.PUBREV.PUBMDR;
		this.PUBMDR = this.PUBREV.PUBMDR;
		this.PUBREV_PUBMJR = this.PUBREV.PUBMJR;
		this.PUBMJR = this.PUBREV.PUBMJR;
      this.PUBVAR = ral_reg_DWC_DDRPHYA_DRTUB0_PUBVAR::type_id::create("PUBVAR",,get_full_name());
      if(this.PUBVAR.has_coverage(UVM_CVR_ALL))
      	this.PUBVAR.cg_bits.option.name = {get_name(), ".", "PUBVAR_bits"};
      this.PUBVAR.configure(this, null, "");
      this.PUBVAR.build();
      this.default_map.add_reg(this.PUBVAR, `UVM_REG_ADDR_WIDTH'hEF, "RO", 0);
		this.PUBVAR_PUBVAR = this.PUBVAR.PUBVAR;
      this.DfiFreqXlat0 = ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat0::type_id::create("DfiFreqXlat0",,get_full_name());
      if(this.DfiFreqXlat0.has_coverage(UVM_CVR_ALL))
      	this.DfiFreqXlat0.cg_bits.option.name = {get_name(), ".", "DfiFreqXlat0_bits"};
      this.DfiFreqXlat0.configure(this, null, "");
      this.DfiFreqXlat0.build();
      this.default_map.add_reg(this.DfiFreqXlat0, `UVM_REG_ADDR_WIDTH'hF0, "RW", 0);
		this.DfiFreqXlat0_DfiFreqXlatVal0 = this.DfiFreqXlat0.DfiFreqXlatVal0;
		this.DfiFreqXlatVal0 = this.DfiFreqXlat0.DfiFreqXlatVal0;
		this.DfiFreqXlat0_DfiFreqXlatVal1 = this.DfiFreqXlat0.DfiFreqXlatVal1;
		this.DfiFreqXlatVal1 = this.DfiFreqXlat0.DfiFreqXlatVal1;
		this.DfiFreqXlat0_DfiFreqXlatVal2 = this.DfiFreqXlat0.DfiFreqXlatVal2;
		this.DfiFreqXlatVal2 = this.DfiFreqXlat0.DfiFreqXlatVal2;
		this.DfiFreqXlat0_DfiFreqXlatVal3 = this.DfiFreqXlat0.DfiFreqXlatVal3;
		this.DfiFreqXlatVal3 = this.DfiFreqXlat0.DfiFreqXlatVal3;
      this.DfiFreqXlat1 = ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat1::type_id::create("DfiFreqXlat1",,get_full_name());
      if(this.DfiFreqXlat1.has_coverage(UVM_CVR_ALL))
      	this.DfiFreqXlat1.cg_bits.option.name = {get_name(), ".", "DfiFreqXlat1_bits"};
      this.DfiFreqXlat1.configure(this, null, "");
      this.DfiFreqXlat1.build();
      this.default_map.add_reg(this.DfiFreqXlat1, `UVM_REG_ADDR_WIDTH'hF1, "RW", 0);
		this.DfiFreqXlat1_DfiFreqXlatVal4 = this.DfiFreqXlat1.DfiFreqXlatVal4;
		this.DfiFreqXlatVal4 = this.DfiFreqXlat1.DfiFreqXlatVal4;
		this.DfiFreqXlat1_DfiFreqXlatVal5 = this.DfiFreqXlat1.DfiFreqXlatVal5;
		this.DfiFreqXlatVal5 = this.DfiFreqXlat1.DfiFreqXlatVal5;
		this.DfiFreqXlat1_DfiFreqXlatVal6 = this.DfiFreqXlat1.DfiFreqXlatVal6;
		this.DfiFreqXlatVal6 = this.DfiFreqXlat1.DfiFreqXlatVal6;
		this.DfiFreqXlat1_DfiFreqXlatVal7 = this.DfiFreqXlat1.DfiFreqXlatVal7;
		this.DfiFreqXlatVal7 = this.DfiFreqXlat1.DfiFreqXlatVal7;
      this.DfiFreqXlat2 = ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat2::type_id::create("DfiFreqXlat2",,get_full_name());
      if(this.DfiFreqXlat2.has_coverage(UVM_CVR_ALL))
      	this.DfiFreqXlat2.cg_bits.option.name = {get_name(), ".", "DfiFreqXlat2_bits"};
      this.DfiFreqXlat2.configure(this, null, "");
      this.DfiFreqXlat2.build();
      this.default_map.add_reg(this.DfiFreqXlat2, `UVM_REG_ADDR_WIDTH'hF2, "RW", 0);
		this.DfiFreqXlat2_DfiFreqXlatVal8 = this.DfiFreqXlat2.DfiFreqXlatVal8;
		this.DfiFreqXlatVal8 = this.DfiFreqXlat2.DfiFreqXlatVal8;
		this.DfiFreqXlat2_DfiFreqXlatVal9 = this.DfiFreqXlat2.DfiFreqXlatVal9;
		this.DfiFreqXlatVal9 = this.DfiFreqXlat2.DfiFreqXlatVal9;
		this.DfiFreqXlat2_DfiFreqXlatVal10 = this.DfiFreqXlat2.DfiFreqXlatVal10;
		this.DfiFreqXlatVal10 = this.DfiFreqXlat2.DfiFreqXlatVal10;
		this.DfiFreqXlat2_DfiFreqXlatVal11 = this.DfiFreqXlat2.DfiFreqXlatVal11;
		this.DfiFreqXlatVal11 = this.DfiFreqXlat2.DfiFreqXlatVal11;
      this.DfiFreqXlat3 = ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat3::type_id::create("DfiFreqXlat3",,get_full_name());
      if(this.DfiFreqXlat3.has_coverage(UVM_CVR_ALL))
      	this.DfiFreqXlat3.cg_bits.option.name = {get_name(), ".", "DfiFreqXlat3_bits"};
      this.DfiFreqXlat3.configure(this, null, "");
      this.DfiFreqXlat3.build();
      this.default_map.add_reg(this.DfiFreqXlat3, `UVM_REG_ADDR_WIDTH'hF3, "RW", 0);
		this.DfiFreqXlat3_DfiFreqXlatVal12 = this.DfiFreqXlat3.DfiFreqXlatVal12;
		this.DfiFreqXlatVal12 = this.DfiFreqXlat3.DfiFreqXlatVal12;
		this.DfiFreqXlat3_DfiFreqXlatVal13 = this.DfiFreqXlat3.DfiFreqXlatVal13;
		this.DfiFreqXlatVal13 = this.DfiFreqXlat3.DfiFreqXlatVal13;
		this.DfiFreqXlat3_DfiFreqXlatVal14 = this.DfiFreqXlat3.DfiFreqXlatVal14;
		this.DfiFreqXlatVal14 = this.DfiFreqXlat3.DfiFreqXlatVal14;
		this.DfiFreqXlat3_DfiFreqXlatVal15 = this.DfiFreqXlat3.DfiFreqXlatVal15;
		this.DfiFreqXlatVal15 = this.DfiFreqXlat3.DfiFreqXlatVal15;
      this.DfiFreqXlat4 = ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat4::type_id::create("DfiFreqXlat4",,get_full_name());
      if(this.DfiFreqXlat4.has_coverage(UVM_CVR_ALL))
      	this.DfiFreqXlat4.cg_bits.option.name = {get_name(), ".", "DfiFreqXlat4_bits"};
      this.DfiFreqXlat4.configure(this, null, "");
      this.DfiFreqXlat4.build();
      this.default_map.add_reg(this.DfiFreqXlat4, `UVM_REG_ADDR_WIDTH'hF4, "RW", 0);
		this.DfiFreqXlat4_DfiFreqXlatVal16 = this.DfiFreqXlat4.DfiFreqXlatVal16;
		this.DfiFreqXlatVal16 = this.DfiFreqXlat4.DfiFreqXlatVal16;
		this.DfiFreqXlat4_DfiFreqXlatVal17 = this.DfiFreqXlat4.DfiFreqXlatVal17;
		this.DfiFreqXlatVal17 = this.DfiFreqXlat4.DfiFreqXlatVal17;
		this.DfiFreqXlat4_DfiFreqXlatVal18 = this.DfiFreqXlat4.DfiFreqXlatVal18;
		this.DfiFreqXlatVal18 = this.DfiFreqXlat4.DfiFreqXlatVal18;
		this.DfiFreqXlat4_DfiFreqXlatVal19 = this.DfiFreqXlat4.DfiFreqXlatVal19;
		this.DfiFreqXlatVal19 = this.DfiFreqXlat4.DfiFreqXlatVal19;
      this.DfiFreqXlat5 = ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat5::type_id::create("DfiFreqXlat5",,get_full_name());
      if(this.DfiFreqXlat5.has_coverage(UVM_CVR_ALL))
      	this.DfiFreqXlat5.cg_bits.option.name = {get_name(), ".", "DfiFreqXlat5_bits"};
      this.DfiFreqXlat5.configure(this, null, "");
      this.DfiFreqXlat5.build();
      this.default_map.add_reg(this.DfiFreqXlat5, `UVM_REG_ADDR_WIDTH'hF5, "RW", 0);
		this.DfiFreqXlat5_DfiFreqXlatVal20 = this.DfiFreqXlat5.DfiFreqXlatVal20;
		this.DfiFreqXlatVal20 = this.DfiFreqXlat5.DfiFreqXlatVal20;
		this.DfiFreqXlat5_DfiFreqXlatVal21 = this.DfiFreqXlat5.DfiFreqXlatVal21;
		this.DfiFreqXlatVal21 = this.DfiFreqXlat5.DfiFreqXlatVal21;
		this.DfiFreqXlat5_DfiFreqXlatVal22 = this.DfiFreqXlat5.DfiFreqXlatVal22;
		this.DfiFreqXlatVal22 = this.DfiFreqXlat5.DfiFreqXlatVal22;
		this.DfiFreqXlat5_DfiFreqXlatVal23 = this.DfiFreqXlat5.DfiFreqXlatVal23;
		this.DfiFreqXlatVal23 = this.DfiFreqXlat5.DfiFreqXlatVal23;
      this.DfiFreqXlat6 = ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat6::type_id::create("DfiFreqXlat6",,get_full_name());
      if(this.DfiFreqXlat6.has_coverage(UVM_CVR_ALL))
      	this.DfiFreqXlat6.cg_bits.option.name = {get_name(), ".", "DfiFreqXlat6_bits"};
      this.DfiFreqXlat6.configure(this, null, "");
      this.DfiFreqXlat6.build();
      this.default_map.add_reg(this.DfiFreqXlat6, `UVM_REG_ADDR_WIDTH'hF6, "RW", 0);
		this.DfiFreqXlat6_DfiFreqXlatVal24 = this.DfiFreqXlat6.DfiFreqXlatVal24;
		this.DfiFreqXlatVal24 = this.DfiFreqXlat6.DfiFreqXlatVal24;
		this.DfiFreqXlat6_DfiFreqXlatVal25 = this.DfiFreqXlat6.DfiFreqXlatVal25;
		this.DfiFreqXlatVal25 = this.DfiFreqXlat6.DfiFreqXlatVal25;
		this.DfiFreqXlat6_DfiFreqXlatVal26 = this.DfiFreqXlat6.DfiFreqXlatVal26;
		this.DfiFreqXlatVal26 = this.DfiFreqXlat6.DfiFreqXlatVal26;
		this.DfiFreqXlat6_DfiFreqXlatVal27 = this.DfiFreqXlat6.DfiFreqXlatVal27;
		this.DfiFreqXlatVal27 = this.DfiFreqXlat6.DfiFreqXlatVal27;
      this.DfiFreqXlat7 = ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat7::type_id::create("DfiFreqXlat7",,get_full_name());
      if(this.DfiFreqXlat7.has_coverage(UVM_CVR_ALL))
      	this.DfiFreqXlat7.cg_bits.option.name = {get_name(), ".", "DfiFreqXlat7_bits"};
      this.DfiFreqXlat7.configure(this, null, "");
      this.DfiFreqXlat7.build();
      this.default_map.add_reg(this.DfiFreqXlat7, `UVM_REG_ADDR_WIDTH'hF7, "RW", 0);
		this.DfiFreqXlat7_DfiFreqXlatVal28 = this.DfiFreqXlat7.DfiFreqXlatVal28;
		this.DfiFreqXlatVal28 = this.DfiFreqXlat7.DfiFreqXlatVal28;
		this.DfiFreqXlat7_DfiFreqXlatVal29 = this.DfiFreqXlat7.DfiFreqXlatVal29;
		this.DfiFreqXlatVal29 = this.DfiFreqXlat7.DfiFreqXlatVal29;
		this.DfiFreqXlat7_DfiFreqXlatVal30 = this.DfiFreqXlat7.DfiFreqXlatVal30;
		this.DfiFreqXlatVal30 = this.DfiFreqXlat7.DfiFreqXlatVal30;
		this.DfiFreqXlat7_DfiFreqXlatVal31 = this.DfiFreqXlat7.DfiFreqXlatVal31;
		this.DfiFreqXlatVal31 = this.DfiFreqXlat7.DfiFreqXlatVal31;
      this.DfiFreqXlat8 = ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat8::type_id::create("DfiFreqXlat8",,get_full_name());
      if(this.DfiFreqXlat8.has_coverage(UVM_CVR_ALL))
      	this.DfiFreqXlat8.cg_bits.option.name = {get_name(), ".", "DfiFreqXlat8_bits"};
      this.DfiFreqXlat8.configure(this, null, "");
      this.DfiFreqXlat8.build();
      this.default_map.add_reg(this.DfiFreqXlat8, `UVM_REG_ADDR_WIDTH'hF8, "RW", 0);
		this.DfiFreqXlat8_DfiFreqXlatVal32 = this.DfiFreqXlat8.DfiFreqXlatVal32;
		this.DfiFreqXlatVal32 = this.DfiFreqXlat8.DfiFreqXlatVal32;
		this.DfiFreqXlat8_DfiFreqXlatVal33 = this.DfiFreqXlat8.DfiFreqXlatVal33;
		this.DfiFreqXlatVal33 = this.DfiFreqXlat8.DfiFreqXlatVal33;
		this.DfiFreqXlat8_DfiFreqXlatVal34 = this.DfiFreqXlat8.DfiFreqXlatVal34;
		this.DfiFreqXlatVal34 = this.DfiFreqXlat8.DfiFreqXlatVal34;
		this.DfiFreqXlat8_DfiFreqXlatVal35 = this.DfiFreqXlat8.DfiFreqXlatVal35;
		this.DfiFreqXlatVal35 = this.DfiFreqXlat8.DfiFreqXlatVal35;
      this.DfiFreqXlat9 = ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat9::type_id::create("DfiFreqXlat9",,get_full_name());
      if(this.DfiFreqXlat9.has_coverage(UVM_CVR_ALL))
      	this.DfiFreqXlat9.cg_bits.option.name = {get_name(), ".", "DfiFreqXlat9_bits"};
      this.DfiFreqXlat9.configure(this, null, "");
      this.DfiFreqXlat9.build();
      this.default_map.add_reg(this.DfiFreqXlat9, `UVM_REG_ADDR_WIDTH'hF9, "RW", 0);
		this.DfiFreqXlat9_DfiFreqXlatVal36 = this.DfiFreqXlat9.DfiFreqXlatVal36;
		this.DfiFreqXlatVal36 = this.DfiFreqXlat9.DfiFreqXlatVal36;
		this.DfiFreqXlat9_DfiFreqXlatVal37 = this.DfiFreqXlat9.DfiFreqXlatVal37;
		this.DfiFreqXlatVal37 = this.DfiFreqXlat9.DfiFreqXlatVal37;
		this.DfiFreqXlat9_DfiFreqXlatVal38 = this.DfiFreqXlat9.DfiFreqXlatVal38;
		this.DfiFreqXlatVal38 = this.DfiFreqXlat9.DfiFreqXlatVal38;
		this.DfiFreqXlat9_DfiFreqXlatVal39 = this.DfiFreqXlat9.DfiFreqXlatVal39;
		this.DfiFreqXlatVal39 = this.DfiFreqXlat9.DfiFreqXlatVal39;
      this.DfiFreqXlat10 = ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat10::type_id::create("DfiFreqXlat10",,get_full_name());
      if(this.DfiFreqXlat10.has_coverage(UVM_CVR_ALL))
      	this.DfiFreqXlat10.cg_bits.option.name = {get_name(), ".", "DfiFreqXlat10_bits"};
      this.DfiFreqXlat10.configure(this, null, "");
      this.DfiFreqXlat10.build();
      this.default_map.add_reg(this.DfiFreqXlat10, `UVM_REG_ADDR_WIDTH'hFA, "RW", 0);
		this.DfiFreqXlat10_DfiFreqXlatVal40 = this.DfiFreqXlat10.DfiFreqXlatVal40;
		this.DfiFreqXlatVal40 = this.DfiFreqXlat10.DfiFreqXlatVal40;
		this.DfiFreqXlat10_DfiFreqXlatVal41 = this.DfiFreqXlat10.DfiFreqXlatVal41;
		this.DfiFreqXlatVal41 = this.DfiFreqXlat10.DfiFreqXlatVal41;
		this.DfiFreqXlat10_DfiFreqXlatVal42 = this.DfiFreqXlat10.DfiFreqXlatVal42;
		this.DfiFreqXlatVal42 = this.DfiFreqXlat10.DfiFreqXlatVal42;
		this.DfiFreqXlat10_DfiFreqXlatVal43 = this.DfiFreqXlat10.DfiFreqXlatVal43;
		this.DfiFreqXlatVal43 = this.DfiFreqXlat10.DfiFreqXlatVal43;
      this.DfiFreqXlat11 = ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat11::type_id::create("DfiFreqXlat11",,get_full_name());
      if(this.DfiFreqXlat11.has_coverage(UVM_CVR_ALL))
      	this.DfiFreqXlat11.cg_bits.option.name = {get_name(), ".", "DfiFreqXlat11_bits"};
      this.DfiFreqXlat11.configure(this, null, "");
      this.DfiFreqXlat11.build();
      this.default_map.add_reg(this.DfiFreqXlat11, `UVM_REG_ADDR_WIDTH'hFB, "RW", 0);
		this.DfiFreqXlat11_DfiFreqXlatVal44 = this.DfiFreqXlat11.DfiFreqXlatVal44;
		this.DfiFreqXlatVal44 = this.DfiFreqXlat11.DfiFreqXlatVal44;
		this.DfiFreqXlat11_DfiFreqXlatVal45 = this.DfiFreqXlat11.DfiFreqXlatVal45;
		this.DfiFreqXlatVal45 = this.DfiFreqXlat11.DfiFreqXlatVal45;
		this.DfiFreqXlat11_DfiFreqXlatVal46 = this.DfiFreqXlat11.DfiFreqXlatVal46;
		this.DfiFreqXlatVal46 = this.DfiFreqXlat11.DfiFreqXlatVal46;
		this.DfiFreqXlat11_DfiFreqXlatVal47 = this.DfiFreqXlat11.DfiFreqXlatVal47;
		this.DfiFreqXlatVal47 = this.DfiFreqXlat11.DfiFreqXlatVal47;
      this.DfiFreqXlat12 = ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat12::type_id::create("DfiFreqXlat12",,get_full_name());
      if(this.DfiFreqXlat12.has_coverage(UVM_CVR_ALL))
      	this.DfiFreqXlat12.cg_bits.option.name = {get_name(), ".", "DfiFreqXlat12_bits"};
      this.DfiFreqXlat12.configure(this, null, "");
      this.DfiFreqXlat12.build();
      this.default_map.add_reg(this.DfiFreqXlat12, `UVM_REG_ADDR_WIDTH'hFC, "RW", 0);
		this.DfiFreqXlat12_DfiFreqXlatVal48 = this.DfiFreqXlat12.DfiFreqXlatVal48;
		this.DfiFreqXlatVal48 = this.DfiFreqXlat12.DfiFreqXlatVal48;
		this.DfiFreqXlat12_DfiFreqXlatVal49 = this.DfiFreqXlat12.DfiFreqXlatVal49;
		this.DfiFreqXlatVal49 = this.DfiFreqXlat12.DfiFreqXlatVal49;
		this.DfiFreqXlat12_DfiFreqXlatVal50 = this.DfiFreqXlat12.DfiFreqXlatVal50;
		this.DfiFreqXlatVal50 = this.DfiFreqXlat12.DfiFreqXlatVal50;
		this.DfiFreqXlat12_DfiFreqXlatVal51 = this.DfiFreqXlat12.DfiFreqXlatVal51;
		this.DfiFreqXlatVal51 = this.DfiFreqXlat12.DfiFreqXlatVal51;
      this.DfiFreqXlat13 = ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat13::type_id::create("DfiFreqXlat13",,get_full_name());
      if(this.DfiFreqXlat13.has_coverage(UVM_CVR_ALL))
      	this.DfiFreqXlat13.cg_bits.option.name = {get_name(), ".", "DfiFreqXlat13_bits"};
      this.DfiFreqXlat13.configure(this, null, "");
      this.DfiFreqXlat13.build();
      this.default_map.add_reg(this.DfiFreqXlat13, `UVM_REG_ADDR_WIDTH'hFD, "RW", 0);
		this.DfiFreqXlat13_DfiFreqXlatVal52 = this.DfiFreqXlat13.DfiFreqXlatVal52;
		this.DfiFreqXlatVal52 = this.DfiFreqXlat13.DfiFreqXlatVal52;
		this.DfiFreqXlat13_DfiFreqXlatVal53 = this.DfiFreqXlat13.DfiFreqXlatVal53;
		this.DfiFreqXlatVal53 = this.DfiFreqXlat13.DfiFreqXlatVal53;
		this.DfiFreqXlat13_DfiFreqXlatVal54 = this.DfiFreqXlat13.DfiFreqXlatVal54;
		this.DfiFreqXlatVal54 = this.DfiFreqXlat13.DfiFreqXlatVal54;
		this.DfiFreqXlat13_DfiFreqXlatVal55 = this.DfiFreqXlat13.DfiFreqXlatVal55;
		this.DfiFreqXlatVal55 = this.DfiFreqXlat13.DfiFreqXlatVal55;
      this.DfiFreqXlat14 = ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat14::type_id::create("DfiFreqXlat14",,get_full_name());
      if(this.DfiFreqXlat14.has_coverage(UVM_CVR_ALL))
      	this.DfiFreqXlat14.cg_bits.option.name = {get_name(), ".", "DfiFreqXlat14_bits"};
      this.DfiFreqXlat14.configure(this, null, "");
      this.DfiFreqXlat14.build();
      this.default_map.add_reg(this.DfiFreqXlat14, `UVM_REG_ADDR_WIDTH'hFE, "RW", 0);
		this.DfiFreqXlat14_DfiFreqXlatVal56 = this.DfiFreqXlat14.DfiFreqXlatVal56;
		this.DfiFreqXlatVal56 = this.DfiFreqXlat14.DfiFreqXlatVal56;
		this.DfiFreqXlat14_DfiFreqXlatVal57 = this.DfiFreqXlat14.DfiFreqXlatVal57;
		this.DfiFreqXlatVal57 = this.DfiFreqXlat14.DfiFreqXlatVal57;
		this.DfiFreqXlat14_DfiFreqXlatVal58 = this.DfiFreqXlat14.DfiFreqXlatVal58;
		this.DfiFreqXlatVal58 = this.DfiFreqXlat14.DfiFreqXlatVal58;
		this.DfiFreqXlat14_DfiFreqXlatVal59 = this.DfiFreqXlat14.DfiFreqXlatVal59;
		this.DfiFreqXlatVal59 = this.DfiFreqXlat14.DfiFreqXlatVal59;
      this.DfiFreqXlat15 = ral_reg_DWC_DDRPHYA_DRTUB0_DfiFreqXlat15::type_id::create("DfiFreqXlat15",,get_full_name());
      if(this.DfiFreqXlat15.has_coverage(UVM_CVR_ALL))
      	this.DfiFreqXlat15.cg_bits.option.name = {get_name(), ".", "DfiFreqXlat15_bits"};
      this.DfiFreqXlat15.configure(this, null, "");
      this.DfiFreqXlat15.build();
      this.default_map.add_reg(this.DfiFreqXlat15, `UVM_REG_ADDR_WIDTH'hFF, "RW", 0);
		this.DfiFreqXlat15_DfiFreqXlatVal60 = this.DfiFreqXlat15.DfiFreqXlatVal60;
		this.DfiFreqXlatVal60 = this.DfiFreqXlat15.DfiFreqXlatVal60;
		this.DfiFreqXlat15_DfiFreqXlatVal61 = this.DfiFreqXlat15.DfiFreqXlatVal61;
		this.DfiFreqXlatVal61 = this.DfiFreqXlat15.DfiFreqXlatVal61;
		this.DfiFreqXlat15_DfiFreqXlatVal62 = this.DfiFreqXlat15.DfiFreqXlatVal62;
		this.DfiFreqXlatVal62 = this.DfiFreqXlat15.DfiFreqXlatVal62;
		this.DfiFreqXlat15_DfiFreqXlatVal63 = this.DfiFreqXlat15.DfiFreqXlatVal63;
		this.DfiFreqXlatVal63 = this.DfiFreqXlat15.DfiFreqXlatVal63;
   endfunction : build

	`uvm_object_utils(ral_block_DWC_DDRPHYA_DRTUB0)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_DDRPHYA_DRTUB0


endpackage
`endif
