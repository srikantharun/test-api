`ifndef RAL_DWC_DDRPHYA_HMDBYTE4_4_P0_PKG
`define RAL_DWC_DDRPHYA_HMDBYTE4_4_P0_PKG

package ral_DWC_DDRPHYA_HMDBYTE4_4_p0_pkg;
import uvm_pkg::*;

class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFECtrlDq_p0 extends uvm_reg;
	rand uvm_reg_field RxDFECtrlDq_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFECtrlDq_p0: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFECtrlDq_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFECtrlDq_p0 = uvm_reg_field::type_id::create("RxDFECtrlDq_p0",,get_full_name());
      this.RxDFECtrlDq_p0.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFECtrlDq_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFECtrlDq_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxCurrAdj extends uvm_reg;
	rand uvm_reg_field RxCurrAdj;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxCurrAdj: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {9'b???????00};
	      wildcard bins bit_0_wr_as_1 = {9'b???????10};
	      wildcard bins bit_0_rd_as_0 = {9'b???????01};
	      wildcard bins bit_0_rd_as_1 = {9'b???????11};
	      wildcard bins bit_1_wr_as_0 = {9'b??????0?0};
	      wildcard bins bit_1_wr_as_1 = {9'b??????1?0};
	      wildcard bins bit_1_rd_as_0 = {9'b??????0?1};
	      wildcard bins bit_1_rd_as_1 = {9'b??????1?1};
	      wildcard bins bit_2_wr_as_0 = {9'b?????0??0};
	      wildcard bins bit_2_wr_as_1 = {9'b?????1??0};
	      wildcard bins bit_2_rd_as_0 = {9'b?????0??1};
	      wildcard bins bit_2_rd_as_1 = {9'b?????1??1};
	      wildcard bins bit_3_wr_as_0 = {9'b????0???0};
	      wildcard bins bit_3_wr_as_1 = {9'b????1???0};
	      wildcard bins bit_3_rd_as_0 = {9'b????0???1};
	      wildcard bins bit_3_rd_as_1 = {9'b????1???1};
	      wildcard bins bit_4_wr_as_0 = {9'b???0????0};
	      wildcard bins bit_4_wr_as_1 = {9'b???1????0};
	      wildcard bins bit_4_rd_as_0 = {9'b???0????1};
	      wildcard bins bit_4_rd_as_1 = {9'b???1????1};
	      wildcard bins bit_5_wr_as_0 = {9'b??0?????0};
	      wildcard bins bit_5_wr_as_1 = {9'b??1?????0};
	      wildcard bins bit_5_rd_as_0 = {9'b??0?????1};
	      wildcard bins bit_5_rd_as_1 = {9'b??1?????1};
	      wildcard bins bit_6_wr_as_0 = {9'b?0??????0};
	      wildcard bins bit_6_wr_as_1 = {9'b?1??????0};
	      wildcard bins bit_6_rd_as_0 = {9'b?0??????1};
	      wildcard bins bit_6_rd_as_1 = {9'b?1??????1};
	      wildcard bins bit_7_wr_as_0 = {9'b0???????0};
	      wildcard bins bit_7_wr_as_1 = {9'b1???????0};
	      wildcard bins bit_7_rd_as_0 = {9'b0???????1};
	      wildcard bins bit_7_rd_as_1 = {9'b1???????1};
	      option.weight = 32;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxCurrAdj");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxCurrAdj = uvm_reg_field::type_id::create("RxCurrAdj",,get_full_name());
      this.RxCurrAdj.configure(this, 8, 0, "RW", 0, 8'h9, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxCurrAdj)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxCurrAdj


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_LpDqPowerDnDly_p0 extends uvm_reg;
	rand uvm_reg_field LpDqPowerDnDly_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   LpDqPowerDnDly_p0: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_LpDqPowerDnDly_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.LpDqPowerDnDly_p0 = uvm_reg_field::type_id::create("LpDqPowerDnDly_p0",,get_full_name());
      this.LpDqPowerDnDly_p0.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_LpDqPowerDnDly_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_LpDqPowerDnDly_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_LpDqPowerDnEn extends uvm_reg;
	rand uvm_reg_field LpDqPowerDnEn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   LpDqPowerDnEn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_LpDqPowerDnEn");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.LpDqPowerDnEn = uvm_reg_field::type_id::create("LpDqPowerDnEn",,get_full_name());
      this.LpDqPowerDnEn.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_LpDqPowerDnEn)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_LpDqPowerDnEn


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RdfPtrChkErrInject extends uvm_reg;
	rand uvm_reg_field RdfPtrChkErrInject;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RdfPtrChkErrInject: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {9'b???????00};
	      wildcard bins bit_0_wr_as_1 = {9'b???????10};
	      wildcard bins bit_0_rd_as_0 = {9'b???????01};
	      wildcard bins bit_0_rd_as_1 = {9'b???????11};
	      wildcard bins bit_1_wr_as_0 = {9'b??????0?0};
	      wildcard bins bit_1_wr_as_1 = {9'b??????1?0};
	      wildcard bins bit_1_rd_as_0 = {9'b??????0?1};
	      wildcard bins bit_1_rd_as_1 = {9'b??????1?1};
	      wildcard bins bit_2_wr_as_0 = {9'b?????0??0};
	      wildcard bins bit_2_wr_as_1 = {9'b?????1??0};
	      wildcard bins bit_2_rd_as_0 = {9'b?????0??1};
	      wildcard bins bit_2_rd_as_1 = {9'b?????1??1};
	      wildcard bins bit_3_wr_as_0 = {9'b????0???0};
	      wildcard bins bit_3_wr_as_1 = {9'b????1???0};
	      wildcard bins bit_3_rd_as_0 = {9'b????0???1};
	      wildcard bins bit_3_rd_as_1 = {9'b????1???1};
	      wildcard bins bit_4_wr_as_0 = {9'b???0????0};
	      wildcard bins bit_4_wr_as_1 = {9'b???1????0};
	      wildcard bins bit_4_rd_as_0 = {9'b???0????1};
	      wildcard bins bit_4_rd_as_1 = {9'b???1????1};
	      wildcard bins bit_5_wr_as_0 = {9'b??0?????0};
	      wildcard bins bit_5_wr_as_1 = {9'b??1?????0};
	      wildcard bins bit_5_rd_as_0 = {9'b??0?????1};
	      wildcard bins bit_5_rd_as_1 = {9'b??1?????1};
	      wildcard bins bit_6_wr_as_0 = {9'b?0??????0};
	      wildcard bins bit_6_wr_as_1 = {9'b?1??????0};
	      wildcard bins bit_6_rd_as_0 = {9'b?0??????1};
	      wildcard bins bit_6_rd_as_1 = {9'b?1??????1};
	      wildcard bins bit_7_wr_as_0 = {9'b0???????0};
	      wildcard bins bit_7_wr_as_1 = {9'b1???????0};
	      wildcard bins bit_7_rd_as_0 = {9'b0???????1};
	      wildcard bins bit_7_rd_as_1 = {9'b1???????1};
	      option.weight = 32;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RdfPtrChkErrInject");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RdfPtrChkErrInject = uvm_reg_field::type_id::create("RdfPtrChkErrInject",,get_full_name());
      this.RdfPtrChkErrInject.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RdfPtrChkErrInject)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RdfPtrChkErrInject


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxDigStrobeMode_p0 extends uvm_reg;
	rand uvm_reg_field DxDigStrobeMode_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DxDigStrobeMode_p0: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_DxDigStrobeMode_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DxDigStrobeMode_p0 = uvm_reg_field::type_id::create("DxDigStrobeMode_p0",,get_full_name());
      this.DxDigStrobeMode_p0.configure(this, 2, 0, "RW", 0, 2'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxDigStrobeMode_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxDigStrobeMode_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxModeCtl extends uvm_reg;
	rand uvm_reg_field RxModeCtl;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxModeCtl: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxModeCtl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxModeCtl = uvm_reg_field::type_id::create("RxModeCtl",,get_full_name());
      this.RxModeCtl.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxModeCtl)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxModeCtl


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxMiscCtl extends uvm_reg;
	rand uvm_reg_field RxOffsetEn;
	rand uvm_reg_field RxGainCtrl;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxOffsetEn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   RxGainCtrl: coverpoint {m_data[3:1], m_is_read} iff(m_be) {
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
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxMiscCtl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxOffsetEn = uvm_reg_field::type_id::create("RxOffsetEn",,get_full_name());
      this.RxOffsetEn.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.RxGainCtrl = uvm_reg_field::type_id::create("RxGainCtrl",,get_full_name());
      this.RxGainCtrl.configure(this, 3, 1, "RW", 0, 3'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxMiscCtl)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxMiscCtl


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DqVregRsvd extends uvm_reg;
	rand uvm_reg_field DqVregRsvd;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DqVregRsvd: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_DqVregRsvd");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DqVregRsvd = uvm_reg_field::type_id::create("DqVregRsvd",,get_full_name());
      this.DqVregRsvd.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DqVregRsvd)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DqVregRsvd


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DqVregRsvdP_p0 extends uvm_reg;
	rand uvm_reg_field DqVregRsvdP_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DqVregRsvdP_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_DqVregRsvdP_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DqVregRsvdP_p0 = uvm_reg_field::type_id::create("DqVregRsvdP_p0",,get_full_name());
      this.DqVregRsvdP_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DqVregRsvdP_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DqVregRsvdP_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_EnaRxStrobeEnB_p0 extends uvm_reg;
	rand uvm_reg_field EnaRxStrobeEnB_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   EnaRxStrobeEnB_p0: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_EnaRxStrobeEnB_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.EnaRxStrobeEnB_p0 = uvm_reg_field::type_id::create("EnaRxStrobeEnB_p0",,get_full_name());
      this.EnaRxStrobeEnB_p0.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_EnaRxStrobeEnB_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_EnaRxStrobeEnB_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_MtestMuxSel extends uvm_reg;
	rand uvm_reg_field MtestMuxSel;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   MtestMuxSel: coverpoint {m_data[9:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {11'b?????????00};
	      wildcard bins bit_0_wr_as_1 = {11'b?????????10};
	      wildcard bins bit_0_rd_as_0 = {11'b?????????01};
	      wildcard bins bit_0_rd_as_1 = {11'b?????????11};
	      wildcard bins bit_1_wr_as_0 = {11'b????????0?0};
	      wildcard bins bit_1_wr_as_1 = {11'b????????1?0};
	      wildcard bins bit_1_rd_as_0 = {11'b????????0?1};
	      wildcard bins bit_1_rd_as_1 = {11'b????????1?1};
	      wildcard bins bit_2_wr_as_0 = {11'b???????0??0};
	      wildcard bins bit_2_wr_as_1 = {11'b???????1??0};
	      wildcard bins bit_2_rd_as_0 = {11'b???????0??1};
	      wildcard bins bit_2_rd_as_1 = {11'b???????1??1};
	      wildcard bins bit_3_wr_as_0 = {11'b??????0???0};
	      wildcard bins bit_3_wr_as_1 = {11'b??????1???0};
	      wildcard bins bit_3_rd_as_0 = {11'b??????0???1};
	      wildcard bins bit_3_rd_as_1 = {11'b??????1???1};
	      wildcard bins bit_4_wr_as_0 = {11'b?????0????0};
	      wildcard bins bit_4_wr_as_1 = {11'b?????1????0};
	      wildcard bins bit_4_rd_as_0 = {11'b?????0????1};
	      wildcard bins bit_4_rd_as_1 = {11'b?????1????1};
	      wildcard bins bit_5_wr_as_0 = {11'b????0?????0};
	      wildcard bins bit_5_wr_as_1 = {11'b????1?????0};
	      wildcard bins bit_5_rd_as_0 = {11'b????0?????1};
	      wildcard bins bit_5_rd_as_1 = {11'b????1?????1};
	      wildcard bins bit_6_wr_as_0 = {11'b???0??????0};
	      wildcard bins bit_6_wr_as_1 = {11'b???1??????0};
	      wildcard bins bit_6_rd_as_0 = {11'b???0??????1};
	      wildcard bins bit_6_rd_as_1 = {11'b???1??????1};
	      wildcard bins bit_7_wr_as_0 = {11'b??0???????0};
	      wildcard bins bit_7_wr_as_1 = {11'b??1???????0};
	      wildcard bins bit_7_rd_as_0 = {11'b??0???????1};
	      wildcard bins bit_7_rd_as_1 = {11'b??1???????1};
	      wildcard bins bit_8_wr_as_0 = {11'b?0????????0};
	      wildcard bins bit_8_wr_as_1 = {11'b?1????????0};
	      wildcard bins bit_8_rd_as_0 = {11'b?0????????1};
	      wildcard bins bit_8_rd_as_1 = {11'b?1????????1};
	      wildcard bins bit_9_wr_as_0 = {11'b0?????????0};
	      wildcard bins bit_9_wr_as_1 = {11'b1?????????0};
	      wildcard bins bit_9_rd_as_0 = {11'b0?????????1};
	      wildcard bins bit_9_rd_as_1 = {11'b1?????????1};
	      option.weight = 40;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_MtestMuxSel");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MtestMuxSel = uvm_reg_field::type_id::create("MtestMuxSel",,get_full_name());
      this.MtestMuxSel.configure(this, 10, 0, "RW", 0, 10'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_MtestMuxSel)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_MtestMuxSel


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDQSlew_p0 extends uvm_reg;
	rand uvm_reg_field TxDQSlewPU;
	rand uvm_reg_field TxDQSlewPD;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDQSlewPU: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   TxDQSlewPD: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxDQSlew_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDQSlewPU = uvm_reg_field::type_id::create("TxDQSlewPU",,get_full_name());
      this.TxDQSlewPU.configure(this, 4, 0, "RW", 0, 4'h1, 1, 0, 0);
      this.TxDQSlewPD = uvm_reg_field::type_id::create("TxDQSlewPD",,get_full_name());
      this.TxDQSlewPD.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDQSlew_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDQSlew_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxPowerDownLightEn extends uvm_reg;
	rand uvm_reg_field RxPowerDownLightEn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxPowerDownLightEn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxPowerDownLightEn");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxPowerDownLightEn = uvm_reg_field::type_id::create("RxPowerDownLightEn",,get_full_name());
      this.RxPowerDownLightEn.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxPowerDownLightEn)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxPowerDownLightEn


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn0 extends uvm_reg;
	rand uvm_reg_field RxDFEBiasSelLn0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFEBiasSelLn0: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFEBiasSelLn0 = uvm_reg_field::type_id::create("RxDFEBiasSelLn0",,get_full_name());
      this.RxDFEBiasSelLn0.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn1 extends uvm_reg;
	rand uvm_reg_field RxDFEBiasSelLn1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFEBiasSelLn1: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn1");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFEBiasSelLn1 = uvm_reg_field::type_id::create("RxDFEBiasSelLn1",,get_full_name());
      this.RxDFEBiasSelLn1.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn1)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn1


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn2 extends uvm_reg;
	rand uvm_reg_field RxDFEBiasSelLn2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFEBiasSelLn2: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFEBiasSelLn2 = uvm_reg_field::type_id::create("RxDFEBiasSelLn2",,get_full_name());
      this.RxDFEBiasSelLn2.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn2)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn3 extends uvm_reg;
	rand uvm_reg_field RxDFEBiasSelLn3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFEBiasSelLn3: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFEBiasSelLn3 = uvm_reg_field::type_id::create("RxDFEBiasSelLn3",,get_full_name());
      this.RxDFEBiasSelLn3.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn3)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn3


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxImpedanceDq_p0 extends uvm_reg;
	rand uvm_reg_field TxStrenCodeDqPU;
	rand uvm_reg_field TxStrenCodeDqPD;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxStrenCodeDqPU: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   TxStrenCodeDqPD: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxImpedanceDq_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxStrenCodeDqPU = uvm_reg_field::type_id::create("TxStrenCodeDqPU",,get_full_name());
      this.TxStrenCodeDqPU.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.TxStrenCodeDqPD = uvm_reg_field::type_id::create("TxStrenCodeDqPD",,get_full_name());
      this.TxStrenCodeDqPD.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxImpedanceDq_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxImpedanceDq_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxImpedanceDqs_p0 extends uvm_reg;
	rand uvm_reg_field TxStrenCodeDqsPUT;
	rand uvm_reg_field TxStrenCodeDqsPUC;
	rand uvm_reg_field TxStrenCodeDqsPDT;
	rand uvm_reg_field TxStrenCodeDqsPDC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxStrenCodeDqsPUT: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   TxStrenCodeDqsPUC: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   TxStrenCodeDqsPDT: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   TxStrenCodeDqsPDC: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxImpedanceDqs_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxStrenCodeDqsPUT = uvm_reg_field::type_id::create("TxStrenCodeDqsPUT",,get_full_name());
      this.TxStrenCodeDqsPUT.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.TxStrenCodeDqsPUC = uvm_reg_field::type_id::create("TxStrenCodeDqsPUC",,get_full_name());
      this.TxStrenCodeDqsPUC.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.TxStrenCodeDqsPDT = uvm_reg_field::type_id::create("TxStrenCodeDqsPDT",,get_full_name());
      this.TxStrenCodeDqsPDT.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.TxStrenCodeDqsPDC = uvm_reg_field::type_id::create("TxStrenCodeDqsPDC",,get_full_name());
      this.TxStrenCodeDqsPDC.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxImpedanceDqs_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxImpedanceDqs_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_OdtImpedanceDq_p0 extends uvm_reg;
	rand uvm_reg_field OdtStrenCodeDqPU;
	rand uvm_reg_field OdtStrenCodeDqPD;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   OdtStrenCodeDqPU: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   OdtStrenCodeDqPD: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_OdtImpedanceDq_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.OdtStrenCodeDqPU = uvm_reg_field::type_id::create("OdtStrenCodeDqPU",,get_full_name());
      this.OdtStrenCodeDqPU.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.OdtStrenCodeDqPD = uvm_reg_field::type_id::create("OdtStrenCodeDqPD",,get_full_name());
      this.OdtStrenCodeDqPD.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_OdtImpedanceDq_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_OdtImpedanceDq_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_OdtImpedanceDqs_p0 extends uvm_reg;
	rand uvm_reg_field OdtStrenCodeDqsPUT;
	rand uvm_reg_field OdtStrenCodeDqsPUC;
	rand uvm_reg_field OdtStrenCodeDqsPDT;
	rand uvm_reg_field OdtStrenCodeDqsPDC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   OdtStrenCodeDqsPUT: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   OdtStrenCodeDqsPUC: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   OdtStrenCodeDqsPDT: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   OdtStrenCodeDqsPDC: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_OdtImpedanceDqs_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.OdtStrenCodeDqsPUT = uvm_reg_field::type_id::create("OdtStrenCodeDqsPUT",,get_full_name());
      this.OdtStrenCodeDqsPUT.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.OdtStrenCodeDqsPUC = uvm_reg_field::type_id::create("OdtStrenCodeDqsPUC",,get_full_name());
      this.OdtStrenCodeDqsPUC.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.OdtStrenCodeDqsPDT = uvm_reg_field::type_id::create("OdtStrenCodeDqsPDT",,get_full_name());
      this.OdtStrenCodeDqsPDT.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.OdtStrenCodeDqsPDC = uvm_reg_field::type_id::create("OdtStrenCodeDqsPDC",,get_full_name());
      this.OdtStrenCodeDqsPDC.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_OdtImpedanceDqs_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_OdtImpedanceDqs_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDQSSeVrefDAC0_p0 extends uvm_reg;
	rand uvm_reg_field RxDQSSeVrefDAC0_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDQSSeVrefDAC0_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {10'b????????00};
	      wildcard bins bit_0_wr_as_1 = {10'b????????10};
	      wildcard bins bit_0_rd_as_0 = {10'b????????01};
	      wildcard bins bit_0_rd_as_1 = {10'b????????11};
	      wildcard bins bit_1_wr_as_0 = {10'b???????0?0};
	      wildcard bins bit_1_wr_as_1 = {10'b???????1?0};
	      wildcard bins bit_1_rd_as_0 = {10'b???????0?1};
	      wildcard bins bit_1_rd_as_1 = {10'b???????1?1};
	      wildcard bins bit_2_wr_as_0 = {10'b??????0??0};
	      wildcard bins bit_2_wr_as_1 = {10'b??????1??0};
	      wildcard bins bit_2_rd_as_0 = {10'b??????0??1};
	      wildcard bins bit_2_rd_as_1 = {10'b??????1??1};
	      wildcard bins bit_3_wr_as_0 = {10'b?????0???0};
	      wildcard bins bit_3_wr_as_1 = {10'b?????1???0};
	      wildcard bins bit_3_rd_as_0 = {10'b?????0???1};
	      wildcard bins bit_3_rd_as_1 = {10'b?????1???1};
	      wildcard bins bit_4_wr_as_0 = {10'b????0????0};
	      wildcard bins bit_4_wr_as_1 = {10'b????1????0};
	      wildcard bins bit_4_rd_as_0 = {10'b????0????1};
	      wildcard bins bit_4_rd_as_1 = {10'b????1????1};
	      wildcard bins bit_5_wr_as_0 = {10'b???0?????0};
	      wildcard bins bit_5_wr_as_1 = {10'b???1?????0};
	      wildcard bins bit_5_rd_as_0 = {10'b???0?????1};
	      wildcard bins bit_5_rd_as_1 = {10'b???1?????1};
	      wildcard bins bit_6_wr_as_0 = {10'b??0??????0};
	      wildcard bins bit_6_wr_as_1 = {10'b??1??????0};
	      wildcard bins bit_6_rd_as_0 = {10'b??0??????1};
	      wildcard bins bit_6_rd_as_1 = {10'b??1??????1};
	      wildcard bins bit_7_wr_as_0 = {10'b?0???????0};
	      wildcard bins bit_7_wr_as_1 = {10'b?1???????0};
	      wildcard bins bit_7_rd_as_0 = {10'b?0???????1};
	      wildcard bins bit_7_rd_as_1 = {10'b?1???????1};
	      wildcard bins bit_8_wr_as_0 = {10'b0????????0};
	      wildcard bins bit_8_wr_as_1 = {10'b1????????0};
	      wildcard bins bit_8_rd_as_0 = {10'b0????????1};
	      wildcard bins bit_8_rd_as_1 = {10'b1????????1};
	      option.weight = 36;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDQSSeVrefDAC0_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDQSSeVrefDAC0_p0 = uvm_reg_field::type_id::create("RxDQSSeVrefDAC0_p0",,get_full_name());
      this.RxDQSSeVrefDAC0_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDQSSeVrefDAC0_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDQSSeVrefDAC0_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDQSCtrl_p0 extends uvm_reg;
	rand uvm_reg_field RxDQSDiffSeVrefDACEn;
	rand uvm_reg_field RxDiffSeCtrl;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDQSDiffSeVrefDACEn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   RxDiffSeCtrl: coverpoint {m_data[2:1], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDQSCtrl_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDQSDiffSeVrefDACEn = uvm_reg_field::type_id::create("RxDQSDiffSeVrefDACEn",,get_full_name());
      this.RxDQSDiffSeVrefDACEn.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.RxDiffSeCtrl = uvm_reg_field::type_id::create("RxDiffSeCtrl",,get_full_name());
      this.RxDiffSeCtrl.configure(this, 2, 1, "RW", 0, 2'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDQSCtrl_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDQSCtrl_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDQDcaMode_p0 extends uvm_reg;
	rand uvm_reg_field TxDQDcaMode_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDQDcaMode_p0: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxDQDcaMode_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDQDcaMode_p0 = uvm_reg_field::type_id::create("TxDQDcaMode_p0",,get_full_name());
      this.TxDQDcaMode_p0.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDQDcaMode_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDQDcaMode_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn0 extends uvm_reg;
	rand uvm_reg_field TxModeCtlDQLn0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxModeCtlDQLn0: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxModeCtlDQLn0 = uvm_reg_field::type_id::create("TxModeCtlDQLn0",,get_full_name());
      this.TxModeCtlDQLn0.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn1 extends uvm_reg;
	rand uvm_reg_field TxModeCtlDQLn1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxModeCtlDQLn1: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn1");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxModeCtlDQLn1 = uvm_reg_field::type_id::create("TxModeCtlDQLn1",,get_full_name());
      this.TxModeCtlDQLn1.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn1)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn1


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn2 extends uvm_reg;
	rand uvm_reg_field TxModeCtlDQLn2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxModeCtlDQLn2: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxModeCtlDQLn2 = uvm_reg_field::type_id::create("TxModeCtlDQLn2",,get_full_name());
      this.TxModeCtlDQLn2.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn2)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn3 extends uvm_reg;
	rand uvm_reg_field TxModeCtlDQLn3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxModeCtlDQLn3: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxModeCtlDQLn3 = uvm_reg_field::type_id::create("TxModeCtlDQLn3",,get_full_name());
      this.TxModeCtlDQLn3.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn3)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn3


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQS extends uvm_reg;
	rand uvm_reg_field TxModeCtlDQS;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxModeCtlDQS: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQS");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxModeCtlDQS = uvm_reg_field::type_id::create("TxModeCtlDQS",,get_full_name());
      this.TxModeCtlDQS.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQS)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQS


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn0 extends uvm_reg;
	rand uvm_reg_field TxPowerDownLn0;
	rand uvm_reg_field RxPowerDownLn0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxPowerDownLn0: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   RxPowerDownLn0: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxPowerDownLn0 = uvm_reg_field::type_id::create("TxPowerDownLn0",,get_full_name());
      this.TxPowerDownLn0.configure(this, 2, 0, "RW", 0, 2'h2, 1, 0, 0);
      this.RxPowerDownLn0 = uvm_reg_field::type_id::create("RxPowerDownLn0",,get_full_name());
      this.RxPowerDownLn0.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn1 extends uvm_reg;
	rand uvm_reg_field TxPowerDownLn1;
	rand uvm_reg_field RxPowerDownLn1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxPowerDownLn1: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   RxPowerDownLn1: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn1");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxPowerDownLn1 = uvm_reg_field::type_id::create("TxPowerDownLn1",,get_full_name());
      this.TxPowerDownLn1.configure(this, 2, 0, "RW", 0, 2'h2, 1, 0, 0);
      this.RxPowerDownLn1 = uvm_reg_field::type_id::create("RxPowerDownLn1",,get_full_name());
      this.RxPowerDownLn1.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn1)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn1


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn2 extends uvm_reg;
	rand uvm_reg_field TxPowerDownLn2;
	rand uvm_reg_field RxPowerDownLn2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxPowerDownLn2: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   RxPowerDownLn2: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxPowerDownLn2 = uvm_reg_field::type_id::create("TxPowerDownLn2",,get_full_name());
      this.TxPowerDownLn2.configure(this, 2, 0, "RW", 0, 2'h2, 1, 0, 0);
      this.RxPowerDownLn2 = uvm_reg_field::type_id::create("RxPowerDownLn2",,get_full_name());
      this.RxPowerDownLn2.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn2)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn3 extends uvm_reg;
	rand uvm_reg_field TxPowerDownLn3;
	rand uvm_reg_field RxPowerDownLn3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxPowerDownLn3: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   RxPowerDownLn3: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxPowerDownLn3 = uvm_reg_field::type_id::create("TxPowerDownLn3",,get_full_name());
      this.TxPowerDownLn3.configure(this, 2, 0, "RW", 0, 2'h2, 1, 0, 0);
      this.RxPowerDownLn3 = uvm_reg_field::type_id::create("RxPowerDownLn3",,get_full_name());
      this.RxPowerDownLn3.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn3)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn3


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownDQS extends uvm_reg;
	rand uvm_reg_field TxPowerDownDQS;
	rand uvm_reg_field RxPowerDownDQS;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxPowerDownDQS: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   RxPowerDownDQS: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownDQS");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxPowerDownDQS = uvm_reg_field::type_id::create("TxPowerDownDQS",,get_full_name());
      this.TxPowerDownDQS.configure(this, 2, 0, "RW", 0, 2'h2, 1, 0, 0);
      this.RxPowerDownDQS = uvm_reg_field::type_id::create("RxPowerDownDQS",,get_full_name());
      this.RxPowerDownDQS.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownDQS)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownDQS


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMDBYTEParityInvert extends uvm_reg;
	rand uvm_reg_field HMDBYTEParityInvert;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HMDBYTEParityInvert: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_HMDBYTEParityInvert");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMDBYTEParityInvert = uvm_reg_field::type_id::create("HMDBYTEParityInvert",,get_full_name());
      this.HMDBYTEParityInvert.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMDBYTEParityInvert)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMDBYTEParityInvert


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMLcdlStatusSel extends uvm_reg;
	rand uvm_reg_field HMLcdlSttsSelReg;
	rand uvm_reg_field HMLcdlSttsSelLane;
	rand uvm_reg_field HMBypMode;
	rand uvm_reg_field HMDQSBypMode;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HMLcdlSttsSelReg: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	   HMLcdlSttsSelLane: coverpoint {m_data[5:3], m_is_read} iff(m_be) {
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
	   HMBypMode: coverpoint {m_data[6:6], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   HMDQSBypMode: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_HMLcdlStatusSel");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMLcdlSttsSelReg = uvm_reg_field::type_id::create("HMLcdlSttsSelReg",,get_full_name());
      this.HMLcdlSttsSelReg.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 0);
      this.HMLcdlSttsSelLane = uvm_reg_field::type_id::create("HMLcdlSttsSelLane",,get_full_name());
      this.HMLcdlSttsSelLane.configure(this, 3, 3, "RW", 0, 3'h0, 1, 0, 0);
      this.HMBypMode = uvm_reg_field::type_id::create("HMBypMode",,get_full_name());
      this.HMBypMode.configure(this, 1, 6, "RW", 0, 1'h0, 1, 0, 0);
      this.HMDQSBypMode = uvm_reg_field::type_id::create("HMDQSBypMode",,get_full_name());
      this.HMDQSBypMode.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMLcdlStatusSel)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMLcdlStatusSel


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMLcdlStatus extends uvm_reg;
	uvm_reg_field LcdlPhaseCal;
	uvm_reg_field LcdlStatus09;
	uvm_reg_field TstLiveLock;
	uvm_reg_field StickyUnlock;
	uvm_reg_field StickyLock;
	uvm_reg_field LcdlStatus15;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   LcdlPhaseCal: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {10'b????????00};
	      wildcard bins bit_0_wr_as_1 = {10'b????????10};
	      wildcard bins bit_0_rd = {10'b?????????1};
	      wildcard bins bit_1_wr_as_0 = {10'b???????0?0};
	      wildcard bins bit_1_wr_as_1 = {10'b???????1?0};
	      wildcard bins bit_1_rd = {10'b?????????1};
	      wildcard bins bit_2_wr_as_0 = {10'b??????0??0};
	      wildcard bins bit_2_wr_as_1 = {10'b??????1??0};
	      wildcard bins bit_2_rd = {10'b?????????1};
	      wildcard bins bit_3_wr_as_0 = {10'b?????0???0};
	      wildcard bins bit_3_wr_as_1 = {10'b?????1???0};
	      wildcard bins bit_3_rd = {10'b?????????1};
	      wildcard bins bit_4_wr_as_0 = {10'b????0????0};
	      wildcard bins bit_4_wr_as_1 = {10'b????1????0};
	      wildcard bins bit_4_rd = {10'b?????????1};
	      wildcard bins bit_5_wr_as_0 = {10'b???0?????0};
	      wildcard bins bit_5_wr_as_1 = {10'b???1?????0};
	      wildcard bins bit_5_rd = {10'b?????????1};
	      wildcard bins bit_6_wr_as_0 = {10'b??0??????0};
	      wildcard bins bit_6_wr_as_1 = {10'b??1??????0};
	      wildcard bins bit_6_rd = {10'b?????????1};
	      wildcard bins bit_7_wr_as_0 = {10'b?0???????0};
	      wildcard bins bit_7_wr_as_1 = {10'b?1???????0};
	      wildcard bins bit_7_rd = {10'b?????????1};
	      wildcard bins bit_8_wr_as_0 = {10'b0????????0};
	      wildcard bins bit_8_wr_as_1 = {10'b1????????0};
	      wildcard bins bit_8_rd = {10'b?????????1};
	      option.weight = 27;
	   }
	   LcdlStatus09: coverpoint {m_data[11:9], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {4'b??00};
	      wildcard bins bit_0_wr_as_1 = {4'b??10};
	      wildcard bins bit_0_rd = {4'b???1};
	      wildcard bins bit_1_wr_as_0 = {4'b?0?0};
	      wildcard bins bit_1_wr_as_1 = {4'b?1?0};
	      wildcard bins bit_1_rd = {4'b???1};
	      wildcard bins bit_2_wr_as_0 = {4'b0??0};
	      wildcard bins bit_2_wr_as_1 = {4'b1??0};
	      wildcard bins bit_2_rd = {4'b???1};
	      option.weight = 9;
	   }
	   TstLiveLock: coverpoint {m_data[12:12], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   StickyUnlock: coverpoint {m_data[13:13], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   StickyLock: coverpoint {m_data[14:14], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   LcdlStatus15: coverpoint {m_data[15:15], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_HMLcdlStatus");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.LcdlPhaseCal = uvm_reg_field::type_id::create("LcdlPhaseCal",,get_full_name());
      this.LcdlPhaseCal.configure(this, 9, 0, "RO", 1, 9'h0, 1, 0, 0);
      this.LcdlStatus09 = uvm_reg_field::type_id::create("LcdlStatus09",,get_full_name());
      this.LcdlStatus09.configure(this, 3, 9, "RO", 1, 3'h0, 1, 0, 0);
      this.TstLiveLock = uvm_reg_field::type_id::create("TstLiveLock",,get_full_name());
      this.TstLiveLock.configure(this, 1, 12, "RO", 1, 1'h0, 1, 0, 0);
      this.StickyUnlock = uvm_reg_field::type_id::create("StickyUnlock",,get_full_name());
      this.StickyUnlock.configure(this, 1, 13, "RO", 1, 1'h0, 1, 0, 0);
      this.StickyLock = uvm_reg_field::type_id::create("StickyLock",,get_full_name());
      this.StickyLock.configure(this, 1, 14, "RO", 1, 1'h0, 1, 0, 0);
      this.LcdlStatus15 = uvm_reg_field::type_id::create("LcdlStatus15",,get_full_name());
      this.LcdlStatus15.configure(this, 1, 15, "RO", 1, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMLcdlStatus)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMLcdlStatus


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMTxLcdlSeed_p0 extends uvm_reg;
	rand uvm_reg_field HMTxLcdlSeed_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HMTxLcdlSeed_p0: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_HMTxLcdlSeed_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMTxLcdlSeed_p0 = uvm_reg_field::type_id::create("HMTxLcdlSeed_p0",,get_full_name());
      this.HMTxLcdlSeed_p0.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMTxLcdlSeed_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMTxLcdlSeed_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMRxLcdlSeed_p0 extends uvm_reg;
	rand uvm_reg_field HMRxLcdlSeed_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HMRxLcdlSeed_p0: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_HMRxLcdlSeed_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMRxLcdlSeed_p0 = uvm_reg_field::type_id::create("HMRxLcdlSeed_p0",,get_full_name());
      this.HMRxLcdlSeed_p0.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMRxLcdlSeed_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMRxLcdlSeed_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMDBYTELcdlCalDeltaStepEn extends uvm_reg;
	rand uvm_reg_field TxLcdlCalDeltaStepEn;
	rand uvm_reg_field RxLcdlCalDeltaStepEn;
	rand uvm_reg_field RxReplicaLcdlCalDeltaStepEn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxLcdlCalDeltaStepEn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   RxLcdlCalDeltaStepEn: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   RxReplicaLcdlCalDeltaStepEn: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_HMDBYTELcdlCalDeltaStepEn");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxLcdlCalDeltaStepEn = uvm_reg_field::type_id::create("TxLcdlCalDeltaStepEn",,get_full_name());
      this.TxLcdlCalDeltaStepEn.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.RxLcdlCalDeltaStepEn = uvm_reg_field::type_id::create("RxLcdlCalDeltaStepEn",,get_full_name());
      this.RxLcdlCalDeltaStepEn.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.RxReplicaLcdlCalDeltaStepEn = uvm_reg_field::type_id::create("RxReplicaLcdlCalDeltaStepEn",,get_full_name());
      this.RxReplicaLcdlCalDeltaStepEn.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMDBYTELcdlCalDeltaStepEn)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMDBYTELcdlCalDeltaStepEn


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_LcdlMonitorCtl_p0 extends uvm_reg;
	rand uvm_reg_field StickyUnlckThrshld;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   StickyUnlckThrshld: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_LcdlMonitorCtl_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.StickyUnlckThrshld = uvm_reg_field::type_id::create("StickyUnlckThrshld",,get_full_name());
      this.StickyUnlckThrshld.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_LcdlMonitorCtl_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_LcdlMonitorCtl_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMDBYTELcdlCalDeltaMM_p0 extends uvm_reg;
	rand uvm_reg_field TxLcdlCalDeltaMM;
	rand uvm_reg_field RxLcdlCalDeltaMM;
	rand uvm_reg_field RxReplicaLcdlCalDeltaMM;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxLcdlCalDeltaMM: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	   RxLcdlCalDeltaMM: coverpoint {m_data[9:5], m_is_read} iff(m_be) {
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
	   RxReplicaLcdlCalDeltaMM: coverpoint {m_data[14:10], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_HMDBYTELcdlCalDeltaMM_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxLcdlCalDeltaMM = uvm_reg_field::type_id::create("TxLcdlCalDeltaMM",,get_full_name());
      this.TxLcdlCalDeltaMM.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 0);
      this.RxLcdlCalDeltaMM = uvm_reg_field::type_id::create("RxLcdlCalDeltaMM",,get_full_name());
      this.RxLcdlCalDeltaMM.configure(this, 5, 5, "RW", 0, 5'h0, 1, 0, 0);
      this.RxReplicaLcdlCalDeltaMM = uvm_reg_field::type_id::create("RxReplicaLcdlCalDeltaMM",,get_full_name());
      this.RxReplicaLcdlCalDeltaMM.configure(this, 5, 10, "RW", 0, 5'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMDBYTELcdlCalDeltaMM_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMDBYTELcdlCalDeltaMM_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn0_p0 extends uvm_reg;
	rand uvm_reg_field RxOffsetSelEvenSLn0_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxOffsetSelEvenSLn0_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn0_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxOffsetSelEvenSLn0_p0 = uvm_reg_field::type_id::create("RxOffsetSelEvenSLn0_p0",,get_full_name());
      this.RxOffsetSelEvenSLn0_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn0_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn0_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn1_p0 extends uvm_reg;
	rand uvm_reg_field RxOffsetSelEvenSLn1_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxOffsetSelEvenSLn1_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn1_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxOffsetSelEvenSLn1_p0 = uvm_reg_field::type_id::create("RxOffsetSelEvenSLn1_p0",,get_full_name());
      this.RxOffsetSelEvenSLn1_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn1_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn1_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn2_p0 extends uvm_reg;
	rand uvm_reg_field RxOffsetSelEvenSLn2_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxOffsetSelEvenSLn2_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn2_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxOffsetSelEvenSLn2_p0 = uvm_reg_field::type_id::create("RxOffsetSelEvenSLn2_p0",,get_full_name());
      this.RxOffsetSelEvenSLn2_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn2_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn2_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn3_p0 extends uvm_reg;
	rand uvm_reg_field RxOffsetSelEvenSLn3_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxOffsetSelEvenSLn3_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn3_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxOffsetSelEvenSLn3_p0 = uvm_reg_field::type_id::create("RxOffsetSelEvenSLn3_p0",,get_full_name());
      this.RxOffsetSelEvenSLn3_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn3_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn3_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn0_p0 extends uvm_reg;
	rand uvm_reg_field RxOffsetSelOddSLn0_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxOffsetSelOddSLn0_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn0_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxOffsetSelOddSLn0_p0 = uvm_reg_field::type_id::create("RxOffsetSelOddSLn0_p0",,get_full_name());
      this.RxOffsetSelOddSLn0_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn0_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn0_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn1_p0 extends uvm_reg;
	rand uvm_reg_field RxOffsetSelOddSLn1_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxOffsetSelOddSLn1_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn1_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxOffsetSelOddSLn1_p0 = uvm_reg_field::type_id::create("RxOffsetSelOddSLn1_p0",,get_full_name());
      this.RxOffsetSelOddSLn1_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn1_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn1_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn2_p0 extends uvm_reg;
	rand uvm_reg_field RxOffsetSelOddSLn2_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxOffsetSelOddSLn2_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn2_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxOffsetSelOddSLn2_p0 = uvm_reg_field::type_id::create("RxOffsetSelOddSLn2_p0",,get_full_name());
      this.RxOffsetSelOddSLn2_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn2_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn2_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn3_p0 extends uvm_reg;
	rand uvm_reg_field RxOffsetSelOddSLn3_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxOffsetSelOddSLn3_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn3_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxOffsetSelOddSLn3_p0 = uvm_reg_field::type_id::create("RxOffsetSelOddSLn3_p0",,get_full_name());
      this.RxOffsetSelOddSLn3_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn3_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn3_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxModeX8Sel extends uvm_reg;
	rand uvm_reg_field RxModeX8Sel;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxModeX8Sel: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxModeX8Sel");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxModeX8Sel = uvm_reg_field::type_id::create("RxModeX8Sel",,get_full_name());
      this.RxModeX8Sel.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxModeX8Sel)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxModeX8Sel


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_ScratchPadHMDBYTE extends uvm_reg;
	rand uvm_reg_field ScratchPadHMDBYTE;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ScratchPadHMDBYTE: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_ScratchPadHMDBYTE");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ScratchPadHMDBYTE = uvm_reg_field::type_id::create("ScratchPadHMDBYTE",,get_full_name());
      this.ScratchPadHMDBYTE.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_ScratchPadHMDBYTE)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_ScratchPadHMDBYTE


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_LcdlTstPhase extends uvm_reg;
	rand uvm_reg_field LcdlTstPhase;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   LcdlTstPhase: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {10'b????????00};
	      wildcard bins bit_0_wr_as_1 = {10'b????????10};
	      wildcard bins bit_0_rd_as_0 = {10'b????????01};
	      wildcard bins bit_0_rd_as_1 = {10'b????????11};
	      wildcard bins bit_1_wr_as_0 = {10'b???????0?0};
	      wildcard bins bit_1_wr_as_1 = {10'b???????1?0};
	      wildcard bins bit_1_rd_as_0 = {10'b???????0?1};
	      wildcard bins bit_1_rd_as_1 = {10'b???????1?1};
	      wildcard bins bit_2_wr_as_0 = {10'b??????0??0};
	      wildcard bins bit_2_wr_as_1 = {10'b??????1??0};
	      wildcard bins bit_2_rd_as_0 = {10'b??????0??1};
	      wildcard bins bit_2_rd_as_1 = {10'b??????1??1};
	      wildcard bins bit_3_wr_as_0 = {10'b?????0???0};
	      wildcard bins bit_3_wr_as_1 = {10'b?????1???0};
	      wildcard bins bit_3_rd_as_0 = {10'b?????0???1};
	      wildcard bins bit_3_rd_as_1 = {10'b?????1???1};
	      wildcard bins bit_4_wr_as_0 = {10'b????0????0};
	      wildcard bins bit_4_wr_as_1 = {10'b????1????0};
	      wildcard bins bit_4_rd_as_0 = {10'b????0????1};
	      wildcard bins bit_4_rd_as_1 = {10'b????1????1};
	      wildcard bins bit_5_wr_as_0 = {10'b???0?????0};
	      wildcard bins bit_5_wr_as_1 = {10'b???1?????0};
	      wildcard bins bit_5_rd_as_0 = {10'b???0?????1};
	      wildcard bins bit_5_rd_as_1 = {10'b???1?????1};
	      wildcard bins bit_6_wr_as_0 = {10'b??0??????0};
	      wildcard bins bit_6_wr_as_1 = {10'b??1??????0};
	      wildcard bins bit_6_rd_as_0 = {10'b??0??????1};
	      wildcard bins bit_6_rd_as_1 = {10'b??1??????1};
	      wildcard bins bit_7_wr_as_0 = {10'b?0???????0};
	      wildcard bins bit_7_wr_as_1 = {10'b?1???????0};
	      wildcard bins bit_7_rd_as_0 = {10'b?0???????1};
	      wildcard bins bit_7_rd_as_1 = {10'b?1???????1};
	      wildcard bins bit_8_wr_as_0 = {10'b0????????0};
	      wildcard bins bit_8_wr_as_1 = {10'b1????????0};
	      wildcard bins bit_8_rd_as_0 = {10'b0????????1};
	      wildcard bins bit_8_rd_as_1 = {10'b1????????1};
	      option.weight = 36;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_LcdlTstPhase");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.LcdlTstPhase = uvm_reg_field::type_id::create("LcdlTstPhase",,get_full_name());
      this.LcdlTstPhase.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_LcdlTstPhase)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_LcdlTstPhase


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMRxReplicaLcdlSeed_p0 extends uvm_reg;
	rand uvm_reg_field HMRxReplicaLcdlSeed_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HMRxReplicaLcdlSeed_p0: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_HMRxReplicaLcdlSeed_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMRxReplicaLcdlSeed_p0 = uvm_reg_field::type_id::create("HMRxReplicaLcdlSeed_p0",,get_full_name());
      this.HMRxReplicaLcdlSeed_p0.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMRxReplicaLcdlSeed_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMRxReplicaLcdlSeed_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDiffDcaMode_p0 extends uvm_reg;
	rand uvm_reg_field TxDiffDcaMode_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDiffDcaMode_p0: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxDiffDcaMode_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDiffDcaMode_p0 = uvm_reg_field::type_id::create("TxDiffDcaMode_p0",,get_full_name());
      this.TxDiffDcaMode_p0.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDiffDcaMode_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDiffDcaMode_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxCoreLoopBackMode extends uvm_reg;
	rand uvm_reg_field DxCoreLoopBackMode;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DxCoreLoopBackMode: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_DxCoreLoopBackMode");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DxCoreLoopBackMode = uvm_reg_field::type_id::create("DxCoreLoopBackMode",,get_full_name());
      this.DxCoreLoopBackMode.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxCoreLoopBackMode)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxCoreLoopBackMode


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln0_p0 extends uvm_reg;
	rand uvm_reg_field RxDFETap1SelTg0Ln0_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap1SelTg0Ln0_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln0_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap1SelTg0Ln0_p0 = uvm_reg_field::type_id::create("RxDFETap1SelTg0Ln0_p0",,get_full_name());
      this.RxDFETap1SelTg0Ln0_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln0_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln0_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln0_p0 extends uvm_reg;
	rand uvm_reg_field RxDFETap1SelTg1Ln0_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap1SelTg1Ln0_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln0_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap1SelTg1Ln0_p0 = uvm_reg_field::type_id::create("RxDFETap1SelTg1Ln0_p0",,get_full_name());
      this.RxDFETap1SelTg1Ln0_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln0_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln0_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln0_p0 extends uvm_reg;
	rand uvm_reg_field RxDFETap2SelTg0Ln0_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap2SelTg0Ln0_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln0_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap2SelTg0Ln0_p0 = uvm_reg_field::type_id::create("RxDFETap2SelTg0Ln0_p0",,get_full_name());
      this.RxDFETap2SelTg0Ln0_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln0_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln0_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln0_p0 extends uvm_reg;
	rand uvm_reg_field RxDFETap2SelTg1Ln0_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap2SelTg1Ln0_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln0_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap2SelTg1Ln0_p0 = uvm_reg_field::type_id::create("RxDFETap2SelTg1Ln0_p0",,get_full_name());
      this.RxDFETap2SelTg1Ln0_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln0_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln0_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln1_p0 extends uvm_reg;
	rand uvm_reg_field RxDFETap1SelTg0Ln1_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap1SelTg0Ln1_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln1_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap1SelTg0Ln1_p0 = uvm_reg_field::type_id::create("RxDFETap1SelTg0Ln1_p0",,get_full_name());
      this.RxDFETap1SelTg0Ln1_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln1_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln1_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln1_p0 extends uvm_reg;
	rand uvm_reg_field RxDFETap1SelTg1Ln1_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap1SelTg1Ln1_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln1_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap1SelTg1Ln1_p0 = uvm_reg_field::type_id::create("RxDFETap1SelTg1Ln1_p0",,get_full_name());
      this.RxDFETap1SelTg1Ln1_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln1_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln1_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln1_p0 extends uvm_reg;
	rand uvm_reg_field RxDFETap2SelTg0Ln1_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap2SelTg0Ln1_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln1_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap2SelTg0Ln1_p0 = uvm_reg_field::type_id::create("RxDFETap2SelTg0Ln1_p0",,get_full_name());
      this.RxDFETap2SelTg0Ln1_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln1_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln1_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln1_p0 extends uvm_reg;
	rand uvm_reg_field RxDFETap2SelTg1Ln1_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap2SelTg1Ln1_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln1_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap2SelTg1Ln1_p0 = uvm_reg_field::type_id::create("RxDFETap2SelTg1Ln1_p0",,get_full_name());
      this.RxDFETap2SelTg1Ln1_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln1_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln1_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln2_p0 extends uvm_reg;
	rand uvm_reg_field RxDFETap1SelTg0Ln2_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap1SelTg0Ln2_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln2_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap1SelTg0Ln2_p0 = uvm_reg_field::type_id::create("RxDFETap1SelTg0Ln2_p0",,get_full_name());
      this.RxDFETap1SelTg0Ln2_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln2_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln2_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln2_p0 extends uvm_reg;
	rand uvm_reg_field RxDFETap1SelTg1Ln2_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap1SelTg1Ln2_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln2_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap1SelTg1Ln2_p0 = uvm_reg_field::type_id::create("RxDFETap1SelTg1Ln2_p0",,get_full_name());
      this.RxDFETap1SelTg1Ln2_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln2_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln2_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln2_p0 extends uvm_reg;
	rand uvm_reg_field RxDFETap2SelTg0Ln2_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap2SelTg0Ln2_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln2_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap2SelTg0Ln2_p0 = uvm_reg_field::type_id::create("RxDFETap2SelTg0Ln2_p0",,get_full_name());
      this.RxDFETap2SelTg0Ln2_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln2_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln2_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln2_p0 extends uvm_reg;
	rand uvm_reg_field RxDFETap2SelTg1Ln2_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap2SelTg1Ln2_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln2_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap2SelTg1Ln2_p0 = uvm_reg_field::type_id::create("RxDFETap2SelTg1Ln2_p0",,get_full_name());
      this.RxDFETap2SelTg1Ln2_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln2_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln2_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln3_p0 extends uvm_reg;
	rand uvm_reg_field RxDFETap1SelTg0Ln3_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap1SelTg0Ln3_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln3_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap1SelTg0Ln3_p0 = uvm_reg_field::type_id::create("RxDFETap1SelTg0Ln3_p0",,get_full_name());
      this.RxDFETap1SelTg0Ln3_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln3_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln3_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln3_p0 extends uvm_reg;
	rand uvm_reg_field RxDFETap1SelTg1Ln3_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap1SelTg1Ln3_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln3_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap1SelTg1Ln3_p0 = uvm_reg_field::type_id::create("RxDFETap1SelTg1Ln3_p0",,get_full_name());
      this.RxDFETap1SelTg1Ln3_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln3_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln3_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln3_p0 extends uvm_reg;
	rand uvm_reg_field RxDFETap2SelTg0Ln3_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap2SelTg0Ln3_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln3_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap2SelTg0Ln3_p0 = uvm_reg_field::type_id::create("RxDFETap2SelTg0Ln3_p0",,get_full_name());
      this.RxDFETap2SelTg0Ln3_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln3_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln3_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln3_p0 extends uvm_reg;
	rand uvm_reg_field RxDFETap2SelTg1Ln3_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap2SelTg1Ln3_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln3_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap2SelTg1Ln3_p0 = uvm_reg_field::type_id::create("RxDFETap2SelTg1Ln3_p0",,get_full_name());
      this.RxDFETap2SelTg1Ln3_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln3_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln3_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn0_p0 extends uvm_reg;
	rand uvm_reg_field PclkDCACoarseDqLn0;
	rand uvm_reg_field PclkDCAFineDqLn0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACoarseDqLn0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	   PclkDCAFineDqLn0: coverpoint {m_data[8:5], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn0_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACoarseDqLn0 = uvm_reg_field::type_id::create("PclkDCACoarseDqLn0",,get_full_name());
      this.PclkDCACoarseDqLn0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 0);
      this.PclkDCAFineDqLn0 = uvm_reg_field::type_id::create("PclkDCAFineDqLn0",,get_full_name());
      this.PclkDCAFineDqLn0.configure(this, 4, 5, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn0_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn0_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn1_p0 extends uvm_reg;
	rand uvm_reg_field PclkDCACoarseDqLn1;
	rand uvm_reg_field PclkDCAFineDqLn1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACoarseDqLn1: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	   PclkDCAFineDqLn1: coverpoint {m_data[8:5], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn1_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACoarseDqLn1 = uvm_reg_field::type_id::create("PclkDCACoarseDqLn1",,get_full_name());
      this.PclkDCACoarseDqLn1.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 0);
      this.PclkDCAFineDqLn1 = uvm_reg_field::type_id::create("PclkDCAFineDqLn1",,get_full_name());
      this.PclkDCAFineDqLn1.configure(this, 4, 5, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn1_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn1_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn2_p0 extends uvm_reg;
	rand uvm_reg_field PclkDCACoarseDqLn2;
	rand uvm_reg_field PclkDCAFineDqLn2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACoarseDqLn2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	   PclkDCAFineDqLn2: coverpoint {m_data[8:5], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn2_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACoarseDqLn2 = uvm_reg_field::type_id::create("PclkDCACoarseDqLn2",,get_full_name());
      this.PclkDCACoarseDqLn2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 0);
      this.PclkDCAFineDqLn2 = uvm_reg_field::type_id::create("PclkDCAFineDqLn2",,get_full_name());
      this.PclkDCAFineDqLn2.configure(this, 4, 5, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn2_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn2_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn3_p0 extends uvm_reg;
	rand uvm_reg_field PclkDCACoarseDqLn3;
	rand uvm_reg_field PclkDCAFineDqLn3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACoarseDqLn3: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	   PclkDCAFineDqLn3: coverpoint {m_data[8:5], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn3_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACoarseDqLn3 = uvm_reg_field::type_id::create("PclkDCACoarseDqLn3",,get_full_name());
      this.PclkDCACoarseDqLn3.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 0);
      this.PclkDCAFineDqLn3 = uvm_reg_field::type_id::create("PclkDCAFineDqLn3",,get_full_name());
      this.PclkDCAFineDqLn3.configure(this, 4, 5, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn3_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn3_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDQS_p0 extends uvm_reg;
	rand uvm_reg_field PclkDCACoarseDQS;
	rand uvm_reg_field PclkDCAFineDQS;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACoarseDQS: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	   PclkDCAFineDQS: coverpoint {m_data[8:5], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDQS_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACoarseDQS = uvm_reg_field::type_id::create("PclkDCACoarseDQS",,get_full_name());
      this.PclkDCACoarseDQS.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 0);
      this.PclkDCAFineDQS = uvm_reg_field::type_id::create("PclkDCAFineDQS",,get_full_name());
      this.PclkDCAFineDQS.configure(this, 4, 5, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDQS_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDQS_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HardMacroModeSel extends uvm_reg;
	rand uvm_reg_field HardMacroModeSel;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HardMacroModeSel: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_HardMacroModeSel");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HardMacroModeSel = uvm_reg_field::type_id::create("HardMacroModeSel",,get_full_name());
      this.HardMacroModeSel.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HardMacroModeSel)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HardMacroModeSel


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxFuncMode extends uvm_reg;
	rand uvm_reg_field TxFuncMode;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxFuncMode: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxFuncMode");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxFuncMode = uvm_reg_field::type_id::create("TxFuncMode",,get_full_name());
      this.TxFuncMode.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxFuncMode)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxFuncMode


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMReserved0 extends uvm_reg;
	rand uvm_reg_field HMReserved0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HMReserved0: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_HMReserved0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMReserved0 = uvm_reg_field::type_id::create("HMReserved0",,get_full_name());
      this.HMReserved0.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMReserved0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMReserved0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMReservedP1_p0 extends uvm_reg;
	rand uvm_reg_field HMReservedP1_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HMReservedP1_p0: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {9'b???????00};
	      wildcard bins bit_0_wr_as_1 = {9'b???????10};
	      wildcard bins bit_0_rd_as_0 = {9'b???????01};
	      wildcard bins bit_0_rd_as_1 = {9'b???????11};
	      wildcard bins bit_1_wr_as_0 = {9'b??????0?0};
	      wildcard bins bit_1_wr_as_1 = {9'b??????1?0};
	      wildcard bins bit_1_rd_as_0 = {9'b??????0?1};
	      wildcard bins bit_1_rd_as_1 = {9'b??????1?1};
	      wildcard bins bit_2_wr_as_0 = {9'b?????0??0};
	      wildcard bins bit_2_wr_as_1 = {9'b?????1??0};
	      wildcard bins bit_2_rd_as_0 = {9'b?????0??1};
	      wildcard bins bit_2_rd_as_1 = {9'b?????1??1};
	      wildcard bins bit_3_wr_as_0 = {9'b????0???0};
	      wildcard bins bit_3_wr_as_1 = {9'b????1???0};
	      wildcard bins bit_3_rd_as_0 = {9'b????0???1};
	      wildcard bins bit_3_rd_as_1 = {9'b????1???1};
	      wildcard bins bit_4_wr_as_0 = {9'b???0????0};
	      wildcard bins bit_4_wr_as_1 = {9'b???1????0};
	      wildcard bins bit_4_rd_as_0 = {9'b???0????1};
	      wildcard bins bit_4_rd_as_1 = {9'b???1????1};
	      wildcard bins bit_5_wr_as_0 = {9'b??0?????0};
	      wildcard bins bit_5_wr_as_1 = {9'b??1?????0};
	      wildcard bins bit_5_rd_as_0 = {9'b??0?????1};
	      wildcard bins bit_5_rd_as_1 = {9'b??1?????1};
	      wildcard bins bit_6_wr_as_0 = {9'b?0??????0};
	      wildcard bins bit_6_wr_as_1 = {9'b?1??????0};
	      wildcard bins bit_6_rd_as_0 = {9'b?0??????1};
	      wildcard bins bit_6_rd_as_1 = {9'b?1??????1};
	      wildcard bins bit_7_wr_as_0 = {9'b0???????0};
	      wildcard bins bit_7_wr_as_1 = {9'b1???????0};
	      wildcard bins bit_7_rd_as_0 = {9'b0???????1};
	      wildcard bins bit_7_rd_as_1 = {9'b1???????1};
	      option.weight = 32;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_HMReservedP1_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMReservedP1_p0 = uvm_reg_field::type_id::create("HMReservedP1_p0",,get_full_name());
      this.HMReservedP1_p0.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMReservedP1_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMReservedP1_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCATxLcdlPhase_p0 extends uvm_reg;
	rand uvm_reg_field PclkDCATxLcdlPhase_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCATxLcdlPhase_p0: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {8'b??????00};
	      wildcard bins bit_0_wr_as_1 = {8'b??????10};
	      wildcard bins bit_0_rd_as_0 = {8'b??????01};
	      wildcard bins bit_0_rd_as_1 = {8'b??????11};
	      wildcard bins bit_1_wr_as_0 = {8'b?????0?0};
	      wildcard bins bit_1_wr_as_1 = {8'b?????1?0};
	      wildcard bins bit_1_rd_as_0 = {8'b?????0?1};
	      wildcard bins bit_1_rd_as_1 = {8'b?????1?1};
	      wildcard bins bit_2_wr_as_0 = {8'b????0??0};
	      wildcard bins bit_2_wr_as_1 = {8'b????1??0};
	      wildcard bins bit_2_rd_as_0 = {8'b????0??1};
	      wildcard bins bit_2_rd_as_1 = {8'b????1??1};
	      wildcard bins bit_3_wr_as_0 = {8'b???0???0};
	      wildcard bins bit_3_wr_as_1 = {8'b???1???0};
	      wildcard bins bit_3_rd_as_0 = {8'b???0???1};
	      wildcard bins bit_3_rd_as_1 = {8'b???1???1};
	      wildcard bins bit_4_wr_as_0 = {8'b??0????0};
	      wildcard bins bit_4_wr_as_1 = {8'b??1????0};
	      wildcard bins bit_4_rd_as_0 = {8'b??0????1};
	      wildcard bins bit_4_rd_as_1 = {8'b??1????1};
	      wildcard bins bit_5_wr_as_0 = {8'b?0?????0};
	      wildcard bins bit_5_wr_as_1 = {8'b?1?????0};
	      wildcard bins bit_5_rd_as_0 = {8'b?0?????1};
	      wildcard bins bit_5_rd_as_1 = {8'b?1?????1};
	      wildcard bins bit_6_wr_as_0 = {8'b0??????0};
	      wildcard bins bit_6_wr_as_1 = {8'b1??????0};
	      wildcard bins bit_6_rd_as_0 = {8'b0??????1};
	      wildcard bins bit_6_rd_as_1 = {8'b1??????1};
	      option.weight = 28;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCATxLcdlPhase_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCATxLcdlPhase_p0 = uvm_reg_field::type_id::create("PclkDCATxLcdlPhase_p0",,get_full_name());
      this.PclkDCATxLcdlPhase_p0.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCATxLcdlPhase_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCATxLcdlPhase_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxReplicaLcdlDbgCntl2 extends uvm_reg;
	rand uvm_reg_field RxReplicaLcdlStickyUnlockThreshold;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxReplicaLcdlStickyUnlockThreshold: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxReplicaLcdlDbgCntl2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxReplicaLcdlStickyUnlockThreshold = uvm_reg_field::type_id::create("RxReplicaLcdlStickyUnlockThreshold",,get_full_name());
      this.RxReplicaLcdlStickyUnlockThreshold.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxReplicaLcdlDbgCntl2)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxReplicaLcdlDbgCntl2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxReplicaLcdlCalPhase extends uvm_reg;
	rand uvm_reg_field RxReplicaLcdlCalPhase;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxReplicaLcdlCalPhase: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {10'b????????00};
	      wildcard bins bit_0_wr_as_1 = {10'b????????10};
	      wildcard bins bit_0_rd_as_0 = {10'b????????01};
	      wildcard bins bit_0_rd_as_1 = {10'b????????11};
	      wildcard bins bit_1_wr_as_0 = {10'b???????0?0};
	      wildcard bins bit_1_wr_as_1 = {10'b???????1?0};
	      wildcard bins bit_1_rd_as_0 = {10'b???????0?1};
	      wildcard bins bit_1_rd_as_1 = {10'b???????1?1};
	      wildcard bins bit_2_wr_as_0 = {10'b??????0??0};
	      wildcard bins bit_2_wr_as_1 = {10'b??????1??0};
	      wildcard bins bit_2_rd_as_0 = {10'b??????0??1};
	      wildcard bins bit_2_rd_as_1 = {10'b??????1??1};
	      wildcard bins bit_3_wr_as_0 = {10'b?????0???0};
	      wildcard bins bit_3_wr_as_1 = {10'b?????1???0};
	      wildcard bins bit_3_rd_as_0 = {10'b?????0???1};
	      wildcard bins bit_3_rd_as_1 = {10'b?????1???1};
	      wildcard bins bit_4_wr_as_0 = {10'b????0????0};
	      wildcard bins bit_4_wr_as_1 = {10'b????1????0};
	      wildcard bins bit_4_rd_as_0 = {10'b????0????1};
	      wildcard bins bit_4_rd_as_1 = {10'b????1????1};
	      wildcard bins bit_5_wr_as_0 = {10'b???0?????0};
	      wildcard bins bit_5_wr_as_1 = {10'b???1?????0};
	      wildcard bins bit_5_rd_as_0 = {10'b???0?????1};
	      wildcard bins bit_5_rd_as_1 = {10'b???1?????1};
	      wildcard bins bit_6_wr_as_0 = {10'b??0??????0};
	      wildcard bins bit_6_wr_as_1 = {10'b??1??????0};
	      wildcard bins bit_6_rd_as_0 = {10'b??0??????1};
	      wildcard bins bit_6_rd_as_1 = {10'b??1??????1};
	      wildcard bins bit_7_wr_as_0 = {10'b?0???????0};
	      wildcard bins bit_7_wr_as_1 = {10'b?1???????0};
	      wildcard bins bit_7_rd_as_0 = {10'b?0???????1};
	      wildcard bins bit_7_rd_as_1 = {10'b?1???????1};
	      wildcard bins bit_8_wr_as_0 = {10'b0????????0};
	      wildcard bins bit_8_wr_as_1 = {10'b1????????0};
	      wildcard bins bit_8_rd_as_0 = {10'b0????????1};
	      wildcard bins bit_8_rd_as_1 = {10'b1????????1};
	      option.weight = 36;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxReplicaLcdlCalPhase");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxReplicaLcdlCalPhase = uvm_reg_field::type_id::create("RxReplicaLcdlCalPhase",,get_full_name());
      this.RxReplicaLcdlCalPhase.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxReplicaLcdlCalPhase)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxReplicaLcdlCalPhase


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn0_p0 extends uvm_reg;
	rand uvm_reg_field PclkDCDOffsetDqLn0_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCDOffsetDqLn0_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn0_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCDOffsetDqLn0_p0 = uvm_reg_field::type_id::create("PclkDCDOffsetDqLn0_p0",,get_full_name());
      this.PclkDCDOffsetDqLn0_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn0_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn0_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn1_p0 extends uvm_reg;
	rand uvm_reg_field PclkDCDOffsetDqLn1_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCDOffsetDqLn1_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn1_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCDOffsetDqLn1_p0 = uvm_reg_field::type_id::create("PclkDCDOffsetDqLn1_p0",,get_full_name());
      this.PclkDCDOffsetDqLn1_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn1_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn1_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn2_p0 extends uvm_reg;
	rand uvm_reg_field PclkDCDOffsetDqLn2_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCDOffsetDqLn2_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn2_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCDOffsetDqLn2_p0 = uvm_reg_field::type_id::create("PclkDCDOffsetDqLn2_p0",,get_full_name());
      this.PclkDCDOffsetDqLn2_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn2_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn2_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn3_p0 extends uvm_reg;
	rand uvm_reg_field PclkDCDOffsetDqLn3_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCDOffsetDqLn3_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn3_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCDOffsetDqLn3_p0 = uvm_reg_field::type_id::create("PclkDCDOffsetDqLn3_p0",,get_full_name());
      this.PclkDCDOffsetDqLn3_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn3_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn3_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDQS_p0 extends uvm_reg;
	rand uvm_reg_field PclkDCDOffsetDQS_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCDOffsetDQS_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDQS_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCDOffsetDQS_p0 = uvm_reg_field::type_id::create("PclkDCDOffsetDQS_p0",,get_full_name());
      this.PclkDCDOffsetDQS_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDQS_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDQS_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn0 extends uvm_reg;
	uvm_reg_field PclkDCACalSampDqLn0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACalSampDqLn0: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACalSampDqLn0 = uvm_reg_field::type_id::create("PclkDCACalSampDqLn0",,get_full_name());
      this.PclkDCACalSampDqLn0.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn1 extends uvm_reg;
	uvm_reg_field PclkDCACalSampDqLn1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACalSampDqLn1: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn1");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACalSampDqLn1 = uvm_reg_field::type_id::create("PclkDCACalSampDqLn1",,get_full_name());
      this.PclkDCACalSampDqLn1.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn1)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn1


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn2 extends uvm_reg;
	uvm_reg_field PclkDCACalSampDqLn2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACalSampDqLn2: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACalSampDqLn2 = uvm_reg_field::type_id::create("PclkDCACalSampDqLn2",,get_full_name());
      this.PclkDCACalSampDqLn2.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn2)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn3 extends uvm_reg;
	uvm_reg_field PclkDCACalSampDqLn3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACalSampDqLn3: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACalSampDqLn3 = uvm_reg_field::type_id::create("PclkDCACalSampDqLn3",,get_full_name());
      this.PclkDCACalSampDqLn3.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn3)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn3


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDQS extends uvm_reg;
	uvm_reg_field PclkDCACalSampDQS;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACalSampDQS: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDQS");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACalSampDQS = uvm_reg_field::type_id::create("PclkDCACalSampDQS",,get_full_name());
      this.PclkDCACalSampDQS.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDQS)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDQS


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCAResults extends uvm_reg;
	uvm_reg_field PclkDCADone;
	uvm_reg_field PclkDCASuccessful;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCADone: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   PclkDCASuccessful: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCAResults");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCADone = uvm_reg_field::type_id::create("PclkDCADone",,get_full_name());
      this.PclkDCADone.configure(this, 1, 0, "RO", 1, 1'h0, 1, 0, 0);
      this.PclkDCASuccessful = uvm_reg_field::type_id::create("PclkDCASuccessful",,get_full_name());
      this.PclkDCASuccessful.configure(this, 1, 1, "RO", 1, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCAResults)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCAResults


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn0 extends uvm_reg;
	uvm_reg_field RxFifoWrLocEvnLn0;
	uvm_reg_field RxFifoWrLocOddLn0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxFifoWrLocEvnLn0: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
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
	   RxFifoWrLocOddLn0: coverpoint {m_data[11:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxFifoWrLocEvnLn0 = uvm_reg_field::type_id::create("RxFifoWrLocEvnLn0",,get_full_name());
      this.RxFifoWrLocEvnLn0.configure(this, 6, 0, "RO", 1, 6'h0, 1, 0, 0);
      this.RxFifoWrLocOddLn0 = uvm_reg_field::type_id::create("RxFifoWrLocOddLn0",,get_full_name());
      this.RxFifoWrLocOddLn0.configure(this, 6, 6, "RO", 1, 6'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn1 extends uvm_reg;
	uvm_reg_field RxFifoWrLocEvnLn1;
	uvm_reg_field RxFifoWrLocOddLn1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxFifoWrLocEvnLn1: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
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
	   RxFifoWrLocOddLn1: coverpoint {m_data[11:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn1");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxFifoWrLocEvnLn1 = uvm_reg_field::type_id::create("RxFifoWrLocEvnLn1",,get_full_name());
      this.RxFifoWrLocEvnLn1.configure(this, 6, 0, "RO", 1, 6'h0, 1, 0, 0);
      this.RxFifoWrLocOddLn1 = uvm_reg_field::type_id::create("RxFifoWrLocOddLn1",,get_full_name());
      this.RxFifoWrLocOddLn1.configure(this, 6, 6, "RO", 1, 6'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn1)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn1


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn2 extends uvm_reg;
	uvm_reg_field RxFifoWrLocEvnLn2;
	uvm_reg_field RxFifoWrLocOddLn2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxFifoWrLocEvnLn2: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
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
	   RxFifoWrLocOddLn2: coverpoint {m_data[11:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxFifoWrLocEvnLn2 = uvm_reg_field::type_id::create("RxFifoWrLocEvnLn2",,get_full_name());
      this.RxFifoWrLocEvnLn2.configure(this, 6, 0, "RO", 1, 6'h0, 1, 0, 0);
      this.RxFifoWrLocOddLn2 = uvm_reg_field::type_id::create("RxFifoWrLocOddLn2",,get_full_name());
      this.RxFifoWrLocOddLn2.configure(this, 6, 6, "RO", 1, 6'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn2)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn3 extends uvm_reg;
	uvm_reg_field RxFifoWrLocEvnLn3;
	uvm_reg_field RxFifoWrLocOddLn3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxFifoWrLocEvnLn3: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
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
	   RxFifoWrLocOddLn3: coverpoint {m_data[11:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxFifoWrLocEvnLn3 = uvm_reg_field::type_id::create("RxFifoWrLocEvnLn3",,get_full_name());
      this.RxFifoWrLocEvnLn3.configure(this, 6, 0, "RO", 1, 6'h0, 1, 0, 0);
      this.RxFifoWrLocOddLn3 = uvm_reg_field::type_id::create("RxFifoWrLocOddLn3",,get_full_name());
      this.RxFifoWrLocOddLn3.configure(this, 6, 6, "RO", 1, 6'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn3)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn3


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn0 extends uvm_reg;
	uvm_reg_field RxFifoRdLocLn0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxFifoRdLocLn0: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {8'b??????00};
	      wildcard bins bit_0_wr_as_1 = {8'b??????10};
	      wildcard bins bit_0_rd = {8'b???????1};
	      wildcard bins bit_1_wr_as_0 = {8'b?????0?0};
	      wildcard bins bit_1_wr_as_1 = {8'b?????1?0};
	      wildcard bins bit_1_rd = {8'b???????1};
	      wildcard bins bit_2_wr_as_0 = {8'b????0??0};
	      wildcard bins bit_2_wr_as_1 = {8'b????1??0};
	      wildcard bins bit_2_rd = {8'b???????1};
	      wildcard bins bit_3_wr_as_0 = {8'b???0???0};
	      wildcard bins bit_3_wr_as_1 = {8'b???1???0};
	      wildcard bins bit_3_rd = {8'b???????1};
	      wildcard bins bit_4_wr_as_0 = {8'b??0????0};
	      wildcard bins bit_4_wr_as_1 = {8'b??1????0};
	      wildcard bins bit_4_rd = {8'b???????1};
	      wildcard bins bit_5_wr_as_0 = {8'b?0?????0};
	      wildcard bins bit_5_wr_as_1 = {8'b?1?????0};
	      wildcard bins bit_5_rd = {8'b???????1};
	      wildcard bins bit_6_wr_as_0 = {8'b0??????0};
	      wildcard bins bit_6_wr_as_1 = {8'b1??????0};
	      wildcard bins bit_6_rd = {8'b???????1};
	      option.weight = 21;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxFifoRdLocLn0 = uvm_reg_field::type_id::create("RxFifoRdLocLn0",,get_full_name());
      this.RxFifoRdLocLn0.configure(this, 7, 0, "RO", 1, 7'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn1 extends uvm_reg;
	uvm_reg_field RxFifoRdLocLn1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxFifoRdLocLn1: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {8'b??????00};
	      wildcard bins bit_0_wr_as_1 = {8'b??????10};
	      wildcard bins bit_0_rd = {8'b???????1};
	      wildcard bins bit_1_wr_as_0 = {8'b?????0?0};
	      wildcard bins bit_1_wr_as_1 = {8'b?????1?0};
	      wildcard bins bit_1_rd = {8'b???????1};
	      wildcard bins bit_2_wr_as_0 = {8'b????0??0};
	      wildcard bins bit_2_wr_as_1 = {8'b????1??0};
	      wildcard bins bit_2_rd = {8'b???????1};
	      wildcard bins bit_3_wr_as_0 = {8'b???0???0};
	      wildcard bins bit_3_wr_as_1 = {8'b???1???0};
	      wildcard bins bit_3_rd = {8'b???????1};
	      wildcard bins bit_4_wr_as_0 = {8'b??0????0};
	      wildcard bins bit_4_wr_as_1 = {8'b??1????0};
	      wildcard bins bit_4_rd = {8'b???????1};
	      wildcard bins bit_5_wr_as_0 = {8'b?0?????0};
	      wildcard bins bit_5_wr_as_1 = {8'b?1?????0};
	      wildcard bins bit_5_rd = {8'b???????1};
	      wildcard bins bit_6_wr_as_0 = {8'b0??????0};
	      wildcard bins bit_6_wr_as_1 = {8'b1??????0};
	      wildcard bins bit_6_rd = {8'b???????1};
	      option.weight = 21;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn1");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxFifoRdLocLn1 = uvm_reg_field::type_id::create("RxFifoRdLocLn1",,get_full_name());
      this.RxFifoRdLocLn1.configure(this, 7, 0, "RO", 1, 7'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn1)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn1


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn2 extends uvm_reg;
	uvm_reg_field RxFifoRdLocLn2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxFifoRdLocLn2: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {8'b??????00};
	      wildcard bins bit_0_wr_as_1 = {8'b??????10};
	      wildcard bins bit_0_rd = {8'b???????1};
	      wildcard bins bit_1_wr_as_0 = {8'b?????0?0};
	      wildcard bins bit_1_wr_as_1 = {8'b?????1?0};
	      wildcard bins bit_1_rd = {8'b???????1};
	      wildcard bins bit_2_wr_as_0 = {8'b????0??0};
	      wildcard bins bit_2_wr_as_1 = {8'b????1??0};
	      wildcard bins bit_2_rd = {8'b???????1};
	      wildcard bins bit_3_wr_as_0 = {8'b???0???0};
	      wildcard bins bit_3_wr_as_1 = {8'b???1???0};
	      wildcard bins bit_3_rd = {8'b???????1};
	      wildcard bins bit_4_wr_as_0 = {8'b??0????0};
	      wildcard bins bit_4_wr_as_1 = {8'b??1????0};
	      wildcard bins bit_4_rd = {8'b???????1};
	      wildcard bins bit_5_wr_as_0 = {8'b?0?????0};
	      wildcard bins bit_5_wr_as_1 = {8'b?1?????0};
	      wildcard bins bit_5_rd = {8'b???????1};
	      wildcard bins bit_6_wr_as_0 = {8'b0??????0};
	      wildcard bins bit_6_wr_as_1 = {8'b1??????0};
	      wildcard bins bit_6_rd = {8'b???????1};
	      option.weight = 21;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxFifoRdLocLn2 = uvm_reg_field::type_id::create("RxFifoRdLocLn2",,get_full_name());
      this.RxFifoRdLocLn2.configure(this, 7, 0, "RO", 1, 7'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn2)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn3 extends uvm_reg;
	uvm_reg_field RxFifoRdLocLn3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxFifoRdLocLn3: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {8'b??????00};
	      wildcard bins bit_0_wr_as_1 = {8'b??????10};
	      wildcard bins bit_0_rd = {8'b???????1};
	      wildcard bins bit_1_wr_as_0 = {8'b?????0?0};
	      wildcard bins bit_1_wr_as_1 = {8'b?????1?0};
	      wildcard bins bit_1_rd = {8'b???????1};
	      wildcard bins bit_2_wr_as_0 = {8'b????0??0};
	      wildcard bins bit_2_wr_as_1 = {8'b????1??0};
	      wildcard bins bit_2_rd = {8'b???????1};
	      wildcard bins bit_3_wr_as_0 = {8'b???0???0};
	      wildcard bins bit_3_wr_as_1 = {8'b???1???0};
	      wildcard bins bit_3_rd = {8'b???????1};
	      wildcard bins bit_4_wr_as_0 = {8'b??0????0};
	      wildcard bins bit_4_wr_as_1 = {8'b??1????0};
	      wildcard bins bit_4_rd = {8'b???????1};
	      wildcard bins bit_5_wr_as_0 = {8'b?0?????0};
	      wildcard bins bit_5_wr_as_1 = {8'b?1?????0};
	      wildcard bins bit_5_rd = {8'b???????1};
	      wildcard bins bit_6_wr_as_0 = {8'b0??????0};
	      wildcard bins bit_6_wr_as_1 = {8'b1??????0};
	      wildcard bins bit_6_rd = {8'b???????1};
	      option.weight = 21;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxFifoRdLocLn3 = uvm_reg_field::type_id::create("RxFifoRdLocLn3",,get_full_name());
      this.RxFifoRdLocLn3.configure(this, 7, 0, "RO", 1, 7'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn3)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn3


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCAStatusSel extends uvm_reg;
	rand uvm_reg_field PclkDCADebugLaneSel;
	rand uvm_reg_field PclkDCADebugInfoSel;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCADebugLaneSel: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	   PclkDCADebugInfoSel: coverpoint {m_data[3:3], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCAStatusSel");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCADebugLaneSel = uvm_reg_field::type_id::create("PclkDCADebugLaneSel",,get_full_name());
      this.PclkDCADebugLaneSel.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 0);
      this.PclkDCADebugInfoSel = uvm_reg_field::type_id::create("PclkDCADebugInfoSel",,get_full_name());
      this.PclkDCADebugInfoSel.configure(this, 1, 3, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCAStatusSel)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCAStatusSel


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCAStatusInfo extends uvm_reg;
	uvm_reg_field PclkDCAStatusInfo;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCAStatusInfo: coverpoint {m_data[11:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {13'b???????????00};
	      wildcard bins bit_0_wr_as_1 = {13'b???????????10};
	      wildcard bins bit_0_rd = {13'b????????????1};
	      wildcard bins bit_1_wr_as_0 = {13'b??????????0?0};
	      wildcard bins bit_1_wr_as_1 = {13'b??????????1?0};
	      wildcard bins bit_1_rd = {13'b????????????1};
	      wildcard bins bit_2_wr_as_0 = {13'b?????????0??0};
	      wildcard bins bit_2_wr_as_1 = {13'b?????????1??0};
	      wildcard bins bit_2_rd = {13'b????????????1};
	      wildcard bins bit_3_wr_as_0 = {13'b????????0???0};
	      wildcard bins bit_3_wr_as_1 = {13'b????????1???0};
	      wildcard bins bit_3_rd = {13'b????????????1};
	      wildcard bins bit_4_wr_as_0 = {13'b???????0????0};
	      wildcard bins bit_4_wr_as_1 = {13'b???????1????0};
	      wildcard bins bit_4_rd = {13'b????????????1};
	      wildcard bins bit_5_wr_as_0 = {13'b??????0?????0};
	      wildcard bins bit_5_wr_as_1 = {13'b??????1?????0};
	      wildcard bins bit_5_rd = {13'b????????????1};
	      wildcard bins bit_6_wr_as_0 = {13'b?????0??????0};
	      wildcard bins bit_6_wr_as_1 = {13'b?????1??????0};
	      wildcard bins bit_6_rd = {13'b????????????1};
	      wildcard bins bit_7_wr_as_0 = {13'b????0???????0};
	      wildcard bins bit_7_wr_as_1 = {13'b????1???????0};
	      wildcard bins bit_7_rd = {13'b????????????1};
	      wildcard bins bit_8_wr_as_0 = {13'b???0????????0};
	      wildcard bins bit_8_wr_as_1 = {13'b???1????????0};
	      wildcard bins bit_8_rd = {13'b????????????1};
	      wildcard bins bit_9_wr_as_0 = {13'b??0?????????0};
	      wildcard bins bit_9_wr_as_1 = {13'b??1?????????0};
	      wildcard bins bit_9_rd = {13'b????????????1};
	      wildcard bins bit_10_wr_as_0 = {13'b?0??????????0};
	      wildcard bins bit_10_wr_as_1 = {13'b?1??????????0};
	      wildcard bins bit_10_rd = {13'b????????????1};
	      wildcard bins bit_11_wr_as_0 = {13'b0???????????0};
	      wildcard bins bit_11_wr_as_1 = {13'b1???????????0};
	      wildcard bins bit_11_rd = {13'b????????????1};
	      option.weight = 36;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCAStatusInfo");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCAStatusInfo = uvm_reg_field::type_id::create("PclkDCAStatusInfo",,get_full_name());
      this.PclkDCAStatusInfo.configure(this, 12, 0, "RO", 1, 12'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCAStatusInfo)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCAStatusInfo


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTTg0_p0 extends uvm_reg;
	rand uvm_reg_field TxDcaFinePDTTg0;
	rand uvm_reg_field TxDcaFinePUTTg0;
	rand uvm_reg_field TxDcaCoarseTTg0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaFinePDTTg0: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUTTg0: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   TxDcaCoarseTTg0: coverpoint {m_data[9:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTTg0_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaFinePDTTg0 = uvm_reg_field::type_id::create("TxDcaFinePDTTg0",,get_full_name());
      this.TxDcaFinePDTTg0.configure(this, 4, 0, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePUTTg0 = uvm_reg_field::type_id::create("TxDcaFinePUTTg0",,get_full_name());
      this.TxDcaFinePUTTg0.configure(this, 4, 4, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaCoarseTTg0 = uvm_reg_field::type_id::create("TxDcaCoarseTTg0",,get_full_name());
      this.TxDcaCoarseTTg0.configure(this, 2, 8, "RW", 0, 2'h3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTTg0_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTTg0_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTTg1_p0 extends uvm_reg;
	rand uvm_reg_field TxDcaFinePDTTg1;
	rand uvm_reg_field TxDcaFinePUTTg1;
	rand uvm_reg_field TxDcaCoarseTTg1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaFinePDTTg1: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUTTg1: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   TxDcaCoarseTTg1: coverpoint {m_data[9:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTTg1_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaFinePDTTg1 = uvm_reg_field::type_id::create("TxDcaFinePDTTg1",,get_full_name());
      this.TxDcaFinePDTTg1.configure(this, 4, 0, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePUTTg1 = uvm_reg_field::type_id::create("TxDcaFinePUTTg1",,get_full_name());
      this.TxDcaFinePUTTg1.configure(this, 4, 4, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaCoarseTTg1 = uvm_reg_field::type_id::create("TxDcaCoarseTTg1",,get_full_name());
      this.TxDcaCoarseTTg1.configure(this, 2, 8, "RW", 0, 2'h3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTTg1_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTTg1_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlCTg0_p0 extends uvm_reg;
	rand uvm_reg_field TxDcaFinePDCTg0;
	rand uvm_reg_field TxDcaFinePUCTg0;
	rand uvm_reg_field TxDcaCoarseCTg0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaFinePDCTg0: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUCTg0: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   TxDcaCoarseCTg0: coverpoint {m_data[9:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlCTg0_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaFinePDCTg0 = uvm_reg_field::type_id::create("TxDcaFinePDCTg0",,get_full_name());
      this.TxDcaFinePDCTg0.configure(this, 4, 0, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePUCTg0 = uvm_reg_field::type_id::create("TxDcaFinePUCTg0",,get_full_name());
      this.TxDcaFinePUCTg0.configure(this, 4, 4, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaCoarseCTg0 = uvm_reg_field::type_id::create("TxDcaCoarseCTg0",,get_full_name());
      this.TxDcaCoarseCTg0.configure(this, 2, 8, "RW", 0, 2'h3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlCTg0_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlCTg0_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlCTg1_p0 extends uvm_reg;
	rand uvm_reg_field TxDcaFinePDCTg1;
	rand uvm_reg_field TxDcaFinePUCTg1;
	rand uvm_reg_field TxDcaCoarseCTg1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaFinePDCTg1: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUCTg1: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   TxDcaCoarseCTg1: coverpoint {m_data[9:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlCTg1_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaFinePDCTg1 = uvm_reg_field::type_id::create("TxDcaFinePDCTg1",,get_full_name());
      this.TxDcaFinePDCTg1.configure(this, 4, 0, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePUCTg1 = uvm_reg_field::type_id::create("TxDcaFinePUCTg1",,get_full_name());
      this.TxDcaFinePUCTg1.configure(this, 4, 4, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaCoarseCTg1 = uvm_reg_field::type_id::create("TxDcaCoarseCTg1",,get_full_name());
      this.TxDcaCoarseCTg1.configure(this, 2, 8, "RW", 0, 2'h3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlCTg1_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlCTg1_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlTTg0_p0 extends uvm_reg;
	rand uvm_reg_field RxDcaFinePDTTg0;
	rand uvm_reg_field RxDcaFinePUTTg0;
	rand uvm_reg_field RxDcaCoarseTTg0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDcaFinePDTTg0: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   RxDcaFinePUTTg0: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   RxDcaCoarseTTg0: coverpoint {m_data[9:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlTTg0_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDcaFinePDTTg0 = uvm_reg_field::type_id::create("RxDcaFinePDTTg0",,get_full_name());
      this.RxDcaFinePDTTg0.configure(this, 4, 0, "RW", 0, 4'h6, 1, 0, 0);
      this.RxDcaFinePUTTg0 = uvm_reg_field::type_id::create("RxDcaFinePUTTg0",,get_full_name());
      this.RxDcaFinePUTTg0.configure(this, 4, 4, "RW", 0, 4'h6, 1, 0, 0);
      this.RxDcaCoarseTTg0 = uvm_reg_field::type_id::create("RxDcaCoarseTTg0",,get_full_name());
      this.RxDcaCoarseTTg0.configure(this, 2, 8, "RW", 0, 2'h3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlTTg0_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlTTg0_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlTTg1_p0 extends uvm_reg;
	rand uvm_reg_field RxDcaFinePDTTg1;
	rand uvm_reg_field RxDcaFinePUTTg1;
	rand uvm_reg_field RxDcaCoarseTTg1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDcaFinePDTTg1: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   RxDcaFinePUTTg1: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   RxDcaCoarseTTg1: coverpoint {m_data[9:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlTTg1_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDcaFinePDTTg1 = uvm_reg_field::type_id::create("RxDcaFinePDTTg1",,get_full_name());
      this.RxDcaFinePDTTg1.configure(this, 4, 0, "RW", 0, 4'h6, 1, 0, 0);
      this.RxDcaFinePUTTg1 = uvm_reg_field::type_id::create("RxDcaFinePUTTg1",,get_full_name());
      this.RxDcaFinePUTTg1.configure(this, 4, 4, "RW", 0, 4'h6, 1, 0, 0);
      this.RxDcaCoarseTTg1 = uvm_reg_field::type_id::create("RxDcaCoarseTTg1",,get_full_name());
      this.RxDcaCoarseTTg1.configure(this, 2, 8, "RW", 0, 2'h3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlTTg1_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlTTg1_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlCTg0_p0 extends uvm_reg;
	rand uvm_reg_field RxDcaFinePDCTg0;
	rand uvm_reg_field RxDcaFinePUCTg0;
	rand uvm_reg_field RxDcaCoarseCTg0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDcaFinePDCTg0: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   RxDcaFinePUCTg0: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   RxDcaCoarseCTg0: coverpoint {m_data[9:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlCTg0_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDcaFinePDCTg0 = uvm_reg_field::type_id::create("RxDcaFinePDCTg0",,get_full_name());
      this.RxDcaFinePDCTg0.configure(this, 4, 0, "RW", 0, 4'h6, 1, 0, 0);
      this.RxDcaFinePUCTg0 = uvm_reg_field::type_id::create("RxDcaFinePUCTg0",,get_full_name());
      this.RxDcaFinePUCTg0.configure(this, 4, 4, "RW", 0, 4'h6, 1, 0, 0);
      this.RxDcaCoarseCTg0 = uvm_reg_field::type_id::create("RxDcaCoarseCTg0",,get_full_name());
      this.RxDcaCoarseCTg0.configure(this, 2, 8, "RW", 0, 2'h3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlCTg0_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlCTg0_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlCTg1_p0 extends uvm_reg;
	rand uvm_reg_field RxDcaFinePDCTg1;
	rand uvm_reg_field RxDcaFinePUCTg1;
	rand uvm_reg_field RxDcaCoarseCTg1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDcaFinePDCTg1: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   RxDcaFinePUCTg1: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   RxDcaCoarseCTg1: coverpoint {m_data[9:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlCTg1_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDcaFinePDCTg1 = uvm_reg_field::type_id::create("RxDcaFinePDCTg1",,get_full_name());
      this.RxDcaFinePDCTg1.configure(this, 4, 0, "RW", 0, 4'h6, 1, 0, 0);
      this.RxDcaFinePUCTg1 = uvm_reg_field::type_id::create("RxDcaFinePUCTg1",,get_full_name());
      this.RxDcaFinePUCTg1.configure(this, 4, 4, "RW", 0, 4'h6, 1, 0, 0);
      this.RxDcaCoarseCTg1 = uvm_reg_field::type_id::create("RxDcaCoarseCTg1",,get_full_name());
      this.RxDcaCoarseCTg1.configure(this, 2, 8, "RW", 0, 2'h3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlCTg1_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlCTg1_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCALcdlCalCtrl extends uvm_reg;
	rand uvm_reg_field PclkDCAUseCSRForCalCtrl;
	rand uvm_reg_field PclkDCALcdlCalMode;
	rand uvm_reg_field PclkDCALcdlCalEn;
	rand uvm_reg_field PclkDCALcdlCalPhaseUpdate;
	rand uvm_reg_field PclkDCALcdlCalClkEn;
	rand uvm_reg_field PclkDCALcdlCalSampEn;
	rand uvm_reg_field PclkDCALcdlResetRelock;
	rand uvm_reg_field PclkDCALcdlStopCal;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCAUseCSRForCalCtrl: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PclkDCALcdlCalMode: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PclkDCALcdlCalEn: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PclkDCALcdlCalPhaseUpdate: coverpoint {m_data[3:3], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PclkDCALcdlCalClkEn: coverpoint {m_data[4:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PclkDCALcdlCalSampEn: coverpoint {m_data[5:5], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PclkDCALcdlResetRelock: coverpoint {m_data[6:6], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PclkDCALcdlStopCal: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCALcdlCalCtrl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCAUseCSRForCalCtrl = uvm_reg_field::type_id::create("PclkDCAUseCSRForCalCtrl",,get_full_name());
      this.PclkDCAUseCSRForCalCtrl.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.PclkDCALcdlCalMode = uvm_reg_field::type_id::create("PclkDCALcdlCalMode",,get_full_name());
      this.PclkDCALcdlCalMode.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.PclkDCALcdlCalEn = uvm_reg_field::type_id::create("PclkDCALcdlCalEn",,get_full_name());
      this.PclkDCALcdlCalEn.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
      this.PclkDCALcdlCalPhaseUpdate = uvm_reg_field::type_id::create("PclkDCALcdlCalPhaseUpdate",,get_full_name());
      this.PclkDCALcdlCalPhaseUpdate.configure(this, 1, 3, "RW", 0, 1'h0, 1, 0, 0);
      this.PclkDCALcdlCalClkEn = uvm_reg_field::type_id::create("PclkDCALcdlCalClkEn",,get_full_name());
      this.PclkDCALcdlCalClkEn.configure(this, 1, 4, "RW", 0, 1'h0, 1, 0, 0);
      this.PclkDCALcdlCalSampEn = uvm_reg_field::type_id::create("PclkDCALcdlCalSampEn",,get_full_name());
      this.PclkDCALcdlCalSampEn.configure(this, 1, 5, "RW", 0, 1'h0, 1, 0, 0);
      this.PclkDCALcdlResetRelock = uvm_reg_field::type_id::create("PclkDCALcdlResetRelock",,get_full_name());
      this.PclkDCALcdlResetRelock.configure(this, 1, 6, "RW", 0, 1'h0, 1, 0, 0);
      this.PclkDCALcdlStopCal = uvm_reg_field::type_id::create("PclkDCALcdlStopCal",,get_full_name());
      this.PclkDCALcdlStopCal.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCALcdlCalCtrl)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCALcdlCalCtrl


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntDfiClkIVHM extends uvm_reg;
	rand uvm_reg_field DlyTestCntDfiClkIVHM;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DlyTestCntDfiClkIVHM: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntDfiClkIVHM");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DlyTestCntDfiClkIVHM = uvm_reg_field::type_id::create("DlyTestCntDfiClkIVHM",,get_full_name());
      this.DlyTestCntDfiClkIVHM.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntDfiClkIVHM)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntDfiClkIVHM


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntDfiClkHM extends uvm_reg;
	uvm_reg_field DlyTestCntDfiClkHM;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DlyTestCntDfiClkHM: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntDfiClkHM");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DlyTestCntDfiClkHM = uvm_reg_field::type_id::create("DlyTestCntDfiClkHM",,get_full_name());
      this.DlyTestCntDfiClkHM.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntDfiClkHM)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntDfiClkHM


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntRingOsc extends uvm_reg;
	uvm_reg_field DlyTestCntRingOsc;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DlyTestCntRingOsc: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntRingOsc");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DlyTestCntRingOsc = uvm_reg_field::type_id::create("DlyTestCntRingOsc",,get_full_name());
      this.DlyTestCntRingOsc.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntRingOsc)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntRingOsc


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestSeqHM extends uvm_reg;
	rand uvm_reg_field DlyTestSeqHM;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DlyTestSeqHM: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestSeqHM");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DlyTestSeqHM = uvm_reg_field::type_id::create("DlyTestSeqHM",,get_full_name());
      this.DlyTestSeqHM.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestSeqHM)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestSeqHM


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCALcdlAddDlySampEn_p0 extends uvm_reg;
	rand uvm_reg_field PclkDCALcdlAddDlySampEn_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCALcdlAddDlySampEn_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCALcdlAddDlySampEn_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCALcdlAddDlySampEn_p0 = uvm_reg_field::type_id::create("PclkDCALcdlAddDlySampEn_p0",,get_full_name());
      this.PclkDCALcdlAddDlySampEn_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCALcdlAddDlySampEn_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCALcdlAddDlySampEn_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkEnDQSIO extends uvm_reg;
	rand uvm_reg_field PclkEnDQSIO;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkEnDQSIO: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_PclkEnDQSIO");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkEnDQSIO = uvm_reg_field::type_id::create("PclkEnDQSIO",,get_full_name());
      this.PclkEnDQSIO.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkEnDQSIO)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkEnDQSIO


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln0_p0 extends uvm_reg;
	rand uvm_reg_field TxDcaCoarseTg0Ln0;
	rand uvm_reg_field TxDcaFinePUTg0Ln0;
	rand uvm_reg_field TxDcaFinePDTg0Ln0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaCoarseTg0Ln0: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUTg0Ln0: coverpoint {m_data[5:2], m_is_read} iff(m_be) {
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
	   TxDcaFinePDTg0Ln0: coverpoint {m_data[9:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln0_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaCoarseTg0Ln0 = uvm_reg_field::type_id::create("TxDcaCoarseTg0Ln0",,get_full_name());
      this.TxDcaCoarseTg0Ln0.configure(this, 2, 0, "RW", 0, 2'h3, 1, 0, 0);
      this.TxDcaFinePUTg0Ln0 = uvm_reg_field::type_id::create("TxDcaFinePUTg0Ln0",,get_full_name());
      this.TxDcaFinePUTg0Ln0.configure(this, 4, 2, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePDTg0Ln0 = uvm_reg_field::type_id::create("TxDcaFinePDTg0Ln0",,get_full_name());
      this.TxDcaFinePDTg0Ln0.configure(this, 4, 6, "RW", 0, 4'h6, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln0_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln0_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln0_p0 extends uvm_reg;
	rand uvm_reg_field TxDcaCoarseTg1Ln0;
	rand uvm_reg_field TxDcaFinePUTg1Ln0;
	rand uvm_reg_field TxDcaFinePDTg1Ln0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaCoarseTg1Ln0: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUTg1Ln0: coverpoint {m_data[5:2], m_is_read} iff(m_be) {
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
	   TxDcaFinePDTg1Ln0: coverpoint {m_data[9:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln0_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaCoarseTg1Ln0 = uvm_reg_field::type_id::create("TxDcaCoarseTg1Ln0",,get_full_name());
      this.TxDcaCoarseTg1Ln0.configure(this, 2, 0, "RW", 0, 2'h3, 1, 0, 0);
      this.TxDcaFinePUTg1Ln0 = uvm_reg_field::type_id::create("TxDcaFinePUTg1Ln0",,get_full_name());
      this.TxDcaFinePUTg1Ln0.configure(this, 4, 2, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePDTg1Ln0 = uvm_reg_field::type_id::create("TxDcaFinePDTg1Ln0",,get_full_name());
      this.TxDcaFinePDTg1Ln0.configure(this, 4, 6, "RW", 0, 4'h6, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln0_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln0_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln1_p0 extends uvm_reg;
	rand uvm_reg_field TxDcaCoarseTg0Ln1;
	rand uvm_reg_field TxDcaFinePUTg0Ln1;
	rand uvm_reg_field TxDcaFinePDTg0Ln1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaCoarseTg0Ln1: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUTg0Ln1: coverpoint {m_data[5:2], m_is_read} iff(m_be) {
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
	   TxDcaFinePDTg0Ln1: coverpoint {m_data[9:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln1_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaCoarseTg0Ln1 = uvm_reg_field::type_id::create("TxDcaCoarseTg0Ln1",,get_full_name());
      this.TxDcaCoarseTg0Ln1.configure(this, 2, 0, "RW", 0, 2'h3, 1, 0, 0);
      this.TxDcaFinePUTg0Ln1 = uvm_reg_field::type_id::create("TxDcaFinePUTg0Ln1",,get_full_name());
      this.TxDcaFinePUTg0Ln1.configure(this, 4, 2, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePDTg0Ln1 = uvm_reg_field::type_id::create("TxDcaFinePDTg0Ln1",,get_full_name());
      this.TxDcaFinePDTg0Ln1.configure(this, 4, 6, "RW", 0, 4'h6, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln1_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln1_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln1_p0 extends uvm_reg;
	rand uvm_reg_field TxDcaCoarseTg1Ln1;
	rand uvm_reg_field TxDcaFinePUTg1Ln1;
	rand uvm_reg_field TxDcaFinePDTg1Ln1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaCoarseTg1Ln1: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUTg1Ln1: coverpoint {m_data[5:2], m_is_read} iff(m_be) {
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
	   TxDcaFinePDTg1Ln1: coverpoint {m_data[9:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln1_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaCoarseTg1Ln1 = uvm_reg_field::type_id::create("TxDcaCoarseTg1Ln1",,get_full_name());
      this.TxDcaCoarseTg1Ln1.configure(this, 2, 0, "RW", 0, 2'h3, 1, 0, 0);
      this.TxDcaFinePUTg1Ln1 = uvm_reg_field::type_id::create("TxDcaFinePUTg1Ln1",,get_full_name());
      this.TxDcaFinePUTg1Ln1.configure(this, 4, 2, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePDTg1Ln1 = uvm_reg_field::type_id::create("TxDcaFinePDTg1Ln1",,get_full_name());
      this.TxDcaFinePDTg1Ln1.configure(this, 4, 6, "RW", 0, 4'h6, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln1_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln1_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln2_p0 extends uvm_reg;
	rand uvm_reg_field TxDcaCoarseTg0Ln2;
	rand uvm_reg_field TxDcaFinePUTg0Ln2;
	rand uvm_reg_field TxDcaFinePDTg0Ln2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaCoarseTg0Ln2: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUTg0Ln2: coverpoint {m_data[5:2], m_is_read} iff(m_be) {
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
	   TxDcaFinePDTg0Ln2: coverpoint {m_data[9:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln2_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaCoarseTg0Ln2 = uvm_reg_field::type_id::create("TxDcaCoarseTg0Ln2",,get_full_name());
      this.TxDcaCoarseTg0Ln2.configure(this, 2, 0, "RW", 0, 2'h3, 1, 0, 0);
      this.TxDcaFinePUTg0Ln2 = uvm_reg_field::type_id::create("TxDcaFinePUTg0Ln2",,get_full_name());
      this.TxDcaFinePUTg0Ln2.configure(this, 4, 2, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePDTg0Ln2 = uvm_reg_field::type_id::create("TxDcaFinePDTg0Ln2",,get_full_name());
      this.TxDcaFinePDTg0Ln2.configure(this, 4, 6, "RW", 0, 4'h6, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln2_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln2_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln2_p0 extends uvm_reg;
	rand uvm_reg_field TxDcaCoarseTg1Ln2;
	rand uvm_reg_field TxDcaFinePUTg1Ln2;
	rand uvm_reg_field TxDcaFinePDTg1Ln2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaCoarseTg1Ln2: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUTg1Ln2: coverpoint {m_data[5:2], m_is_read} iff(m_be) {
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
	   TxDcaFinePDTg1Ln2: coverpoint {m_data[9:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln2_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaCoarseTg1Ln2 = uvm_reg_field::type_id::create("TxDcaCoarseTg1Ln2",,get_full_name());
      this.TxDcaCoarseTg1Ln2.configure(this, 2, 0, "RW", 0, 2'h3, 1, 0, 0);
      this.TxDcaFinePUTg1Ln2 = uvm_reg_field::type_id::create("TxDcaFinePUTg1Ln2",,get_full_name());
      this.TxDcaFinePUTg1Ln2.configure(this, 4, 2, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePDTg1Ln2 = uvm_reg_field::type_id::create("TxDcaFinePDTg1Ln2",,get_full_name());
      this.TxDcaFinePDTg1Ln2.configure(this, 4, 6, "RW", 0, 4'h6, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln2_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln2_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln3_p0 extends uvm_reg;
	rand uvm_reg_field TxDcaCoarseTg0Ln3;
	rand uvm_reg_field TxDcaFinePUTg0Ln3;
	rand uvm_reg_field TxDcaFinePDTg0Ln3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaCoarseTg0Ln3: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUTg0Ln3: coverpoint {m_data[5:2], m_is_read} iff(m_be) {
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
	   TxDcaFinePDTg0Ln3: coverpoint {m_data[9:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln3_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaCoarseTg0Ln3 = uvm_reg_field::type_id::create("TxDcaCoarseTg0Ln3",,get_full_name());
      this.TxDcaCoarseTg0Ln3.configure(this, 2, 0, "RW", 0, 2'h3, 1, 0, 0);
      this.TxDcaFinePUTg0Ln3 = uvm_reg_field::type_id::create("TxDcaFinePUTg0Ln3",,get_full_name());
      this.TxDcaFinePUTg0Ln3.configure(this, 4, 2, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePDTg0Ln3 = uvm_reg_field::type_id::create("TxDcaFinePDTg0Ln3",,get_full_name());
      this.TxDcaFinePDTg0Ln3.configure(this, 4, 6, "RW", 0, 4'h6, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln3_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln3_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln3_p0 extends uvm_reg;
	rand uvm_reg_field TxDcaCoarseTg1Ln3;
	rand uvm_reg_field TxDcaFinePUTg1Ln3;
	rand uvm_reg_field TxDcaFinePDTg1Ln3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaCoarseTg1Ln3: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUTg1Ln3: coverpoint {m_data[5:2], m_is_read} iff(m_be) {
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
	   TxDcaFinePDTg1Ln3: coverpoint {m_data[9:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln3_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaCoarseTg1Ln3 = uvm_reg_field::type_id::create("TxDcaCoarseTg1Ln3",,get_full_name());
      this.TxDcaCoarseTg1Ln3.configure(this, 2, 0, "RW", 0, 2'h3, 1, 0, 0);
      this.TxDcaFinePUTg1Ln3 = uvm_reg_field::type_id::create("TxDcaFinePUTg1Ln3",,get_full_name());
      this.TxDcaFinePUTg1Ln3.configure(this, 4, 2, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePDTg1Ln3 = uvm_reg_field::type_id::create("TxDcaFinePDTg1Ln3",,get_full_name());
      this.TxDcaFinePDTg1Ln3.configure(this, 4, 6, "RW", 0, 4'h6, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln3_p0)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln3_p0


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxReplicaLcdlStatus extends uvm_reg;
	uvm_reg_field RxReplicaLcdlFineSnapVal;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxReplicaLcdlFineSnapVal: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {10'b????????00};
	      wildcard bins bit_0_wr_as_1 = {10'b????????10};
	      wildcard bins bit_0_rd = {10'b?????????1};
	      wildcard bins bit_1_wr_as_0 = {10'b???????0?0};
	      wildcard bins bit_1_wr_as_1 = {10'b???????1?0};
	      wildcard bins bit_1_rd = {10'b?????????1};
	      wildcard bins bit_2_wr_as_0 = {10'b??????0??0};
	      wildcard bins bit_2_wr_as_1 = {10'b??????1??0};
	      wildcard bins bit_2_rd = {10'b?????????1};
	      wildcard bins bit_3_wr_as_0 = {10'b?????0???0};
	      wildcard bins bit_3_wr_as_1 = {10'b?????1???0};
	      wildcard bins bit_3_rd = {10'b?????????1};
	      wildcard bins bit_4_wr_as_0 = {10'b????0????0};
	      wildcard bins bit_4_wr_as_1 = {10'b????1????0};
	      wildcard bins bit_4_rd = {10'b?????????1};
	      wildcard bins bit_5_wr_as_0 = {10'b???0?????0};
	      wildcard bins bit_5_wr_as_1 = {10'b???1?????0};
	      wildcard bins bit_5_rd = {10'b?????????1};
	      wildcard bins bit_6_wr_as_0 = {10'b??0??????0};
	      wildcard bins bit_6_wr_as_1 = {10'b??1??????0};
	      wildcard bins bit_6_rd = {10'b?????????1};
	      wildcard bins bit_7_wr_as_0 = {10'b?0???????0};
	      wildcard bins bit_7_wr_as_1 = {10'b?1???????0};
	      wildcard bins bit_7_rd = {10'b?????????1};
	      wildcard bins bit_8_wr_as_0 = {10'b0????????0};
	      wildcard bins bit_8_wr_as_1 = {10'b1????????0};
	      wildcard bins bit_8_rd = {10'b?????????1};
	      option.weight = 27;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_RxReplicaLcdlStatus");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxReplicaLcdlFineSnapVal = uvm_reg_field::type_id::create("RxReplicaLcdlFineSnapVal",,get_full_name());
      this.RxReplicaLcdlFineSnapVal.configure(this, 9, 0, "RO", 1, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxReplicaLcdlStatus)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxReplicaLcdlStatus


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntRingOscSelDX extends uvm_reg;
	rand uvm_reg_field DlyTestCntRingOscSelDX;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DlyTestCntRingOscSelDX: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntRingOscSelDX");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DlyTestCntRingOscSelDX = uvm_reg_field::type_id::create("DlyTestCntRingOscSelDX",,get_full_name());
      this.DlyTestCntRingOscSelDX.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntRingOscSelDX)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntRingOscSelDX


class ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestRingSelDX extends uvm_reg;
	rand uvm_reg_field DlyTestRingSelDX;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DlyTestRingSelDX: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestRingSelDX");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DlyTestRingSelDX = uvm_reg_field::type_id::create("DlyTestRingSelDX",,get_full_name());
      this.DlyTestRingSelDX.configure(this, 6, 0, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestRingSelDX)

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
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestRingSelDX


class ral_block_DWC_DDRPHYA_HMDBYTE4_4_p0 extends uvm_reg_block;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFECtrlDq_p0 RxDFECtrlDq_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxCurrAdj RxCurrAdj;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_LpDqPowerDnDly_p0 LpDqPowerDnDly_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_LpDqPowerDnEn LpDqPowerDnEn;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RdfPtrChkErrInject RdfPtrChkErrInject;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxDigStrobeMode_p0 DxDigStrobeMode_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxModeCtl RxModeCtl;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxMiscCtl RxMiscCtl;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DqVregRsvd DqVregRsvd;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DqVregRsvdP_p0 DqVregRsvdP_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_EnaRxStrobeEnB_p0 EnaRxStrobeEnB_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_MtestMuxSel MtestMuxSel;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDQSlew_p0 TxDQSlew_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxPowerDownLightEn RxPowerDownLightEn;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn0 RxDFEBiasSelLn0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn1 RxDFEBiasSelLn1;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn2 RxDFEBiasSelLn2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn3 RxDFEBiasSelLn3;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxImpedanceDq_p0 TxImpedanceDq_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxImpedanceDqs_p0 TxImpedanceDqs_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_OdtImpedanceDq_p0 OdtImpedanceDq_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_OdtImpedanceDqs_p0 OdtImpedanceDqs_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDQSSeVrefDAC0_p0 RxDQSSeVrefDAC0_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDQSCtrl_p0 RxDQSCtrl_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDQDcaMode_p0 TxDQDcaMode_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn0 TxModeCtlDQLn0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn1 TxModeCtlDQLn1;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn2 TxModeCtlDQLn2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn3 TxModeCtlDQLn3;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQS TxModeCtlDQS;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn0 DxRxPowerDownLn0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn1 DxRxPowerDownLn1;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn2 DxRxPowerDownLn2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn3 DxRxPowerDownLn3;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownDQS DxRxPowerDownDQS;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMDBYTEParityInvert HMDBYTEParityInvert;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMLcdlStatusSel HMLcdlStatusSel;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMLcdlStatus HMLcdlStatus;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMTxLcdlSeed_p0 HMTxLcdlSeed_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMRxLcdlSeed_p0 HMRxLcdlSeed_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMDBYTELcdlCalDeltaStepEn HMDBYTELcdlCalDeltaStepEn;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_LcdlMonitorCtl_p0 LcdlMonitorCtl_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMDBYTELcdlCalDeltaMM_p0 HMDBYTELcdlCalDeltaMM_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn0_p0 RxOffsetSelEvenSLn0_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn1_p0 RxOffsetSelEvenSLn1_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn2_p0 RxOffsetSelEvenSLn2_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn3_p0 RxOffsetSelEvenSLn3_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn0_p0 RxOffsetSelOddSLn0_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn1_p0 RxOffsetSelOddSLn1_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn2_p0 RxOffsetSelOddSLn2_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn3_p0 RxOffsetSelOddSLn3_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxModeX8Sel RxModeX8Sel;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_ScratchPadHMDBYTE ScratchPadHMDBYTE;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_LcdlTstPhase LcdlTstPhase;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMRxReplicaLcdlSeed_p0 HMRxReplicaLcdlSeed_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDiffDcaMode_p0 TxDiffDcaMode_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxCoreLoopBackMode DxCoreLoopBackMode;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln0_p0 RxDFETap1SelTg0Ln0_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln0_p0 RxDFETap1SelTg1Ln0_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln0_p0 RxDFETap2SelTg0Ln0_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln0_p0 RxDFETap2SelTg1Ln0_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln1_p0 RxDFETap1SelTg0Ln1_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln1_p0 RxDFETap1SelTg1Ln1_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln1_p0 RxDFETap2SelTg0Ln1_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln1_p0 RxDFETap2SelTg1Ln1_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln2_p0 RxDFETap1SelTg0Ln2_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln2_p0 RxDFETap1SelTg1Ln2_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln2_p0 RxDFETap2SelTg0Ln2_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln2_p0 RxDFETap2SelTg1Ln2_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln3_p0 RxDFETap1SelTg0Ln3_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln3_p0 RxDFETap1SelTg1Ln3_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln3_p0 RxDFETap2SelTg0Ln3_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln3_p0 RxDFETap2SelTg1Ln3_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn0_p0 PclkDCACodeDqLn0_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn1_p0 PclkDCACodeDqLn1_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn2_p0 PclkDCACodeDqLn2_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn3_p0 PclkDCACodeDqLn3_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDQS_p0 PclkDCACodeDQS_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HardMacroModeSel HardMacroModeSel;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxFuncMode TxFuncMode;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMReserved0 HMReserved0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMReservedP1_p0 HMReservedP1_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCATxLcdlPhase_p0 PclkDCATxLcdlPhase_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxReplicaLcdlDbgCntl2 RxReplicaLcdlDbgCntl2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxReplicaLcdlCalPhase RxReplicaLcdlCalPhase;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn0_p0 PclkDCDOffsetDqLn0_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn1_p0 PclkDCDOffsetDqLn1_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn2_p0 PclkDCDOffsetDqLn2_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn3_p0 PclkDCDOffsetDqLn3_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDQS_p0 PclkDCDOffsetDQS_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn0 PclkDCACalSampDqLn0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn1 PclkDCACalSampDqLn1;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn2 PclkDCACalSampDqLn2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn3 PclkDCACalSampDqLn3;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDQS PclkDCACalSampDQS;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCAResults PclkDCAResults;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn0 RxFifoWrInfoLn0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn1 RxFifoWrInfoLn1;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn2 RxFifoWrInfoLn2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn3 RxFifoWrInfoLn3;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn0 RxFifoRdInfoLn0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn1 RxFifoRdInfoLn1;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn2 RxFifoRdInfoLn2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn3 RxFifoRdInfoLn3;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCAStatusSel PclkDCAStatusSel;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCAStatusInfo PclkDCAStatusInfo;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTTg0_p0 TxDcaCtrlTTg0_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTTg1_p0 TxDcaCtrlTTg1_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlCTg0_p0 TxDcaCtrlCTg0_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlCTg1_p0 TxDcaCtrlCTg1_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlTTg0_p0 RxDcaCtrlTTg0_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlTTg1_p0 RxDcaCtrlTTg1_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlCTg0_p0 RxDcaCtrlCTg0_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlCTg1_p0 RxDcaCtrlCTg1_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCALcdlCalCtrl PclkDCALcdlCalCtrl;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntDfiClkIVHM DlyTestCntDfiClkIVHM;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntDfiClkHM DlyTestCntDfiClkHM;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntRingOsc DlyTestCntRingOsc;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestSeqHM DlyTestSeqHM;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCALcdlAddDlySampEn_p0 PclkDCALcdlAddDlySampEn_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkEnDQSIO PclkEnDQSIO;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln0_p0 TxDcaCtrlTg0Ln0_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln0_p0 TxDcaCtrlTg1Ln0_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln1_p0 TxDcaCtrlTg0Ln1_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln1_p0 TxDcaCtrlTg1Ln1_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln2_p0 TxDcaCtrlTg0Ln2_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln2_p0 TxDcaCtrlTg1Ln2_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln3_p0 TxDcaCtrlTg0Ln3_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln3_p0 TxDcaCtrlTg1Ln3_p0;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxReplicaLcdlStatus RxReplicaLcdlStatus;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntRingOscSelDX DlyTestCntRingOscSelDX;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestRingSelDX DlyTestRingSelDX;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field RxDFECtrlDq_p0_RxDFECtrlDq_p0;
	rand uvm_reg_field RxCurrAdj_RxCurrAdj;
	rand uvm_reg_field LpDqPowerDnDly_p0_LpDqPowerDnDly_p0;
	rand uvm_reg_field LpDqPowerDnEn_LpDqPowerDnEn;
	rand uvm_reg_field RdfPtrChkErrInject_RdfPtrChkErrInject;
	rand uvm_reg_field DxDigStrobeMode_p0_DxDigStrobeMode_p0;
	rand uvm_reg_field RxModeCtl_RxModeCtl;
	rand uvm_reg_field RxMiscCtl_RxOffsetEn;
	rand uvm_reg_field RxOffsetEn;
	rand uvm_reg_field RxMiscCtl_RxGainCtrl;
	rand uvm_reg_field RxGainCtrl;
	rand uvm_reg_field DqVregRsvd_DqVregRsvd;
	rand uvm_reg_field DqVregRsvdP_p0_DqVregRsvdP_p0;
	rand uvm_reg_field EnaRxStrobeEnB_p0_EnaRxStrobeEnB_p0;
	rand uvm_reg_field MtestMuxSel_MtestMuxSel;
	rand uvm_reg_field TxDQSlew_p0_TxDQSlewPU;
	rand uvm_reg_field TxDQSlewPU;
	rand uvm_reg_field TxDQSlew_p0_TxDQSlewPD;
	rand uvm_reg_field TxDQSlewPD;
	rand uvm_reg_field RxPowerDownLightEn_RxPowerDownLightEn;
	rand uvm_reg_field RxDFEBiasSelLn0_RxDFEBiasSelLn0;
	rand uvm_reg_field RxDFEBiasSelLn1_RxDFEBiasSelLn1;
	rand uvm_reg_field RxDFEBiasSelLn2_RxDFEBiasSelLn2;
	rand uvm_reg_field RxDFEBiasSelLn3_RxDFEBiasSelLn3;
	rand uvm_reg_field TxImpedanceDq_p0_TxStrenCodeDqPU;
	rand uvm_reg_field TxStrenCodeDqPU;
	rand uvm_reg_field TxImpedanceDq_p0_TxStrenCodeDqPD;
	rand uvm_reg_field TxStrenCodeDqPD;
	rand uvm_reg_field TxImpedanceDqs_p0_TxStrenCodeDqsPUT;
	rand uvm_reg_field TxStrenCodeDqsPUT;
	rand uvm_reg_field TxImpedanceDqs_p0_TxStrenCodeDqsPUC;
	rand uvm_reg_field TxStrenCodeDqsPUC;
	rand uvm_reg_field TxImpedanceDqs_p0_TxStrenCodeDqsPDT;
	rand uvm_reg_field TxStrenCodeDqsPDT;
	rand uvm_reg_field TxImpedanceDqs_p0_TxStrenCodeDqsPDC;
	rand uvm_reg_field TxStrenCodeDqsPDC;
	rand uvm_reg_field OdtImpedanceDq_p0_OdtStrenCodeDqPU;
	rand uvm_reg_field OdtStrenCodeDqPU;
	rand uvm_reg_field OdtImpedanceDq_p0_OdtStrenCodeDqPD;
	rand uvm_reg_field OdtStrenCodeDqPD;
	rand uvm_reg_field OdtImpedanceDqs_p0_OdtStrenCodeDqsPUT;
	rand uvm_reg_field OdtStrenCodeDqsPUT;
	rand uvm_reg_field OdtImpedanceDqs_p0_OdtStrenCodeDqsPUC;
	rand uvm_reg_field OdtStrenCodeDqsPUC;
	rand uvm_reg_field OdtImpedanceDqs_p0_OdtStrenCodeDqsPDT;
	rand uvm_reg_field OdtStrenCodeDqsPDT;
	rand uvm_reg_field OdtImpedanceDqs_p0_OdtStrenCodeDqsPDC;
	rand uvm_reg_field OdtStrenCodeDqsPDC;
	rand uvm_reg_field RxDQSSeVrefDAC0_p0_RxDQSSeVrefDAC0_p0;
	rand uvm_reg_field RxDQSCtrl_p0_RxDQSDiffSeVrefDACEn;
	rand uvm_reg_field RxDQSDiffSeVrefDACEn;
	rand uvm_reg_field RxDQSCtrl_p0_RxDiffSeCtrl;
	rand uvm_reg_field RxDiffSeCtrl;
	rand uvm_reg_field TxDQDcaMode_p0_TxDQDcaMode_p0;
	rand uvm_reg_field TxModeCtlDQLn0_TxModeCtlDQLn0;
	rand uvm_reg_field TxModeCtlDQLn1_TxModeCtlDQLn1;
	rand uvm_reg_field TxModeCtlDQLn2_TxModeCtlDQLn2;
	rand uvm_reg_field TxModeCtlDQLn3_TxModeCtlDQLn3;
	rand uvm_reg_field TxModeCtlDQS_TxModeCtlDQS;
	rand uvm_reg_field DxRxPowerDownLn0_TxPowerDownLn0;
	rand uvm_reg_field TxPowerDownLn0;
	rand uvm_reg_field DxRxPowerDownLn0_RxPowerDownLn0;
	rand uvm_reg_field RxPowerDownLn0;
	rand uvm_reg_field DxRxPowerDownLn1_TxPowerDownLn1;
	rand uvm_reg_field TxPowerDownLn1;
	rand uvm_reg_field DxRxPowerDownLn1_RxPowerDownLn1;
	rand uvm_reg_field RxPowerDownLn1;
	rand uvm_reg_field DxRxPowerDownLn2_TxPowerDownLn2;
	rand uvm_reg_field TxPowerDownLn2;
	rand uvm_reg_field DxRxPowerDownLn2_RxPowerDownLn2;
	rand uvm_reg_field RxPowerDownLn2;
	rand uvm_reg_field DxRxPowerDownLn3_TxPowerDownLn3;
	rand uvm_reg_field TxPowerDownLn3;
	rand uvm_reg_field DxRxPowerDownLn3_RxPowerDownLn3;
	rand uvm_reg_field RxPowerDownLn3;
	rand uvm_reg_field DxRxPowerDownDQS_TxPowerDownDQS;
	rand uvm_reg_field TxPowerDownDQS;
	rand uvm_reg_field DxRxPowerDownDQS_RxPowerDownDQS;
	rand uvm_reg_field RxPowerDownDQS;
	rand uvm_reg_field HMDBYTEParityInvert_HMDBYTEParityInvert;
	rand uvm_reg_field HMLcdlStatusSel_HMLcdlSttsSelReg;
	rand uvm_reg_field HMLcdlSttsSelReg;
	rand uvm_reg_field HMLcdlStatusSel_HMLcdlSttsSelLane;
	rand uvm_reg_field HMLcdlSttsSelLane;
	rand uvm_reg_field HMLcdlStatusSel_HMBypMode;
	rand uvm_reg_field HMBypMode;
	rand uvm_reg_field HMLcdlStatusSel_HMDQSBypMode;
	rand uvm_reg_field HMDQSBypMode;
	uvm_reg_field HMLcdlStatus_LcdlPhaseCal;
	uvm_reg_field LcdlPhaseCal;
	uvm_reg_field HMLcdlStatus_LcdlStatus09;
	uvm_reg_field LcdlStatus09;
	uvm_reg_field HMLcdlStatus_TstLiveLock;
	uvm_reg_field TstLiveLock;
	uvm_reg_field HMLcdlStatus_StickyUnlock;
	uvm_reg_field StickyUnlock;
	uvm_reg_field HMLcdlStatus_StickyLock;
	uvm_reg_field StickyLock;
	uvm_reg_field HMLcdlStatus_LcdlStatus15;
	uvm_reg_field LcdlStatus15;
	rand uvm_reg_field HMTxLcdlSeed_p0_HMTxLcdlSeed_p0;
	rand uvm_reg_field HMRxLcdlSeed_p0_HMRxLcdlSeed_p0;
	rand uvm_reg_field HMDBYTELcdlCalDeltaStepEn_TxLcdlCalDeltaStepEn;
	rand uvm_reg_field TxLcdlCalDeltaStepEn;
	rand uvm_reg_field HMDBYTELcdlCalDeltaStepEn_RxLcdlCalDeltaStepEn;
	rand uvm_reg_field RxLcdlCalDeltaStepEn;
	rand uvm_reg_field HMDBYTELcdlCalDeltaStepEn_RxReplicaLcdlCalDeltaStepEn;
	rand uvm_reg_field RxReplicaLcdlCalDeltaStepEn;
	rand uvm_reg_field LcdlMonitorCtl_p0_StickyUnlckThrshld;
	rand uvm_reg_field StickyUnlckThrshld;
	rand uvm_reg_field HMDBYTELcdlCalDeltaMM_p0_TxLcdlCalDeltaMM;
	rand uvm_reg_field TxLcdlCalDeltaMM;
	rand uvm_reg_field HMDBYTELcdlCalDeltaMM_p0_RxLcdlCalDeltaMM;
	rand uvm_reg_field RxLcdlCalDeltaMM;
	rand uvm_reg_field HMDBYTELcdlCalDeltaMM_p0_RxReplicaLcdlCalDeltaMM;
	rand uvm_reg_field RxReplicaLcdlCalDeltaMM;
	rand uvm_reg_field RxOffsetSelEvenSLn0_p0_RxOffsetSelEvenSLn0_p0;
	rand uvm_reg_field RxOffsetSelEvenSLn1_p0_RxOffsetSelEvenSLn1_p0;
	rand uvm_reg_field RxOffsetSelEvenSLn2_p0_RxOffsetSelEvenSLn2_p0;
	rand uvm_reg_field RxOffsetSelEvenSLn3_p0_RxOffsetSelEvenSLn3_p0;
	rand uvm_reg_field RxOffsetSelOddSLn0_p0_RxOffsetSelOddSLn0_p0;
	rand uvm_reg_field RxOffsetSelOddSLn1_p0_RxOffsetSelOddSLn1_p0;
	rand uvm_reg_field RxOffsetSelOddSLn2_p0_RxOffsetSelOddSLn2_p0;
	rand uvm_reg_field RxOffsetSelOddSLn3_p0_RxOffsetSelOddSLn3_p0;
	rand uvm_reg_field RxModeX8Sel_RxModeX8Sel;
	rand uvm_reg_field ScratchPadHMDBYTE_ScratchPadHMDBYTE;
	rand uvm_reg_field LcdlTstPhase_LcdlTstPhase;
	rand uvm_reg_field HMRxReplicaLcdlSeed_p0_HMRxReplicaLcdlSeed_p0;
	rand uvm_reg_field TxDiffDcaMode_p0_TxDiffDcaMode_p0;
	rand uvm_reg_field DxCoreLoopBackMode_DxCoreLoopBackMode;
	rand uvm_reg_field RxDFETap1SelTg0Ln0_p0_RxDFETap1SelTg0Ln0_p0;
	rand uvm_reg_field RxDFETap1SelTg1Ln0_p0_RxDFETap1SelTg1Ln0_p0;
	rand uvm_reg_field RxDFETap2SelTg0Ln0_p0_RxDFETap2SelTg0Ln0_p0;
	rand uvm_reg_field RxDFETap2SelTg1Ln0_p0_RxDFETap2SelTg1Ln0_p0;
	rand uvm_reg_field RxDFETap1SelTg0Ln1_p0_RxDFETap1SelTg0Ln1_p0;
	rand uvm_reg_field RxDFETap1SelTg1Ln1_p0_RxDFETap1SelTg1Ln1_p0;
	rand uvm_reg_field RxDFETap2SelTg0Ln1_p0_RxDFETap2SelTg0Ln1_p0;
	rand uvm_reg_field RxDFETap2SelTg1Ln1_p0_RxDFETap2SelTg1Ln1_p0;
	rand uvm_reg_field RxDFETap1SelTg0Ln2_p0_RxDFETap1SelTg0Ln2_p0;
	rand uvm_reg_field RxDFETap1SelTg1Ln2_p0_RxDFETap1SelTg1Ln2_p0;
	rand uvm_reg_field RxDFETap2SelTg0Ln2_p0_RxDFETap2SelTg0Ln2_p0;
	rand uvm_reg_field RxDFETap2SelTg1Ln2_p0_RxDFETap2SelTg1Ln2_p0;
	rand uvm_reg_field RxDFETap1SelTg0Ln3_p0_RxDFETap1SelTg0Ln3_p0;
	rand uvm_reg_field RxDFETap1SelTg1Ln3_p0_RxDFETap1SelTg1Ln3_p0;
	rand uvm_reg_field RxDFETap2SelTg0Ln3_p0_RxDFETap2SelTg0Ln3_p0;
	rand uvm_reg_field RxDFETap2SelTg1Ln3_p0_RxDFETap2SelTg1Ln3_p0;
	rand uvm_reg_field PclkDCACodeDqLn0_p0_PclkDCACoarseDqLn0;
	rand uvm_reg_field PclkDCACoarseDqLn0;
	rand uvm_reg_field PclkDCACodeDqLn0_p0_PclkDCAFineDqLn0;
	rand uvm_reg_field PclkDCAFineDqLn0;
	rand uvm_reg_field PclkDCACodeDqLn1_p0_PclkDCACoarseDqLn1;
	rand uvm_reg_field PclkDCACoarseDqLn1;
	rand uvm_reg_field PclkDCACodeDqLn1_p0_PclkDCAFineDqLn1;
	rand uvm_reg_field PclkDCAFineDqLn1;
	rand uvm_reg_field PclkDCACodeDqLn2_p0_PclkDCACoarseDqLn2;
	rand uvm_reg_field PclkDCACoarseDqLn2;
	rand uvm_reg_field PclkDCACodeDqLn2_p0_PclkDCAFineDqLn2;
	rand uvm_reg_field PclkDCAFineDqLn2;
	rand uvm_reg_field PclkDCACodeDqLn3_p0_PclkDCACoarseDqLn3;
	rand uvm_reg_field PclkDCACoarseDqLn3;
	rand uvm_reg_field PclkDCACodeDqLn3_p0_PclkDCAFineDqLn3;
	rand uvm_reg_field PclkDCAFineDqLn3;
	rand uvm_reg_field PclkDCACodeDQS_p0_PclkDCACoarseDQS;
	rand uvm_reg_field PclkDCACoarseDQS;
	rand uvm_reg_field PclkDCACodeDQS_p0_PclkDCAFineDQS;
	rand uvm_reg_field PclkDCAFineDQS;
	rand uvm_reg_field HardMacroModeSel_HardMacroModeSel;
	rand uvm_reg_field TxFuncMode_TxFuncMode;
	rand uvm_reg_field HMReserved0_HMReserved0;
	rand uvm_reg_field HMReservedP1_p0_HMReservedP1_p0;
	rand uvm_reg_field PclkDCATxLcdlPhase_p0_PclkDCATxLcdlPhase_p0;
	rand uvm_reg_field RxReplicaLcdlDbgCntl2_RxReplicaLcdlStickyUnlockThreshold;
	rand uvm_reg_field RxReplicaLcdlStickyUnlockThreshold;
	rand uvm_reg_field RxReplicaLcdlCalPhase_RxReplicaLcdlCalPhase;
	rand uvm_reg_field PclkDCDOffsetDqLn0_p0_PclkDCDOffsetDqLn0_p0;
	rand uvm_reg_field PclkDCDOffsetDqLn1_p0_PclkDCDOffsetDqLn1_p0;
	rand uvm_reg_field PclkDCDOffsetDqLn2_p0_PclkDCDOffsetDqLn2_p0;
	rand uvm_reg_field PclkDCDOffsetDqLn3_p0_PclkDCDOffsetDqLn3_p0;
	rand uvm_reg_field PclkDCDOffsetDQS_p0_PclkDCDOffsetDQS_p0;
	uvm_reg_field PclkDCACalSampDqLn0_PclkDCACalSampDqLn0;
	uvm_reg_field PclkDCACalSampDqLn1_PclkDCACalSampDqLn1;
	uvm_reg_field PclkDCACalSampDqLn2_PclkDCACalSampDqLn2;
	uvm_reg_field PclkDCACalSampDqLn3_PclkDCACalSampDqLn3;
	uvm_reg_field PclkDCACalSampDQS_PclkDCACalSampDQS;
	uvm_reg_field PclkDCAResults_PclkDCADone;
	uvm_reg_field PclkDCADone;
	uvm_reg_field PclkDCAResults_PclkDCASuccessful;
	uvm_reg_field PclkDCASuccessful;
	uvm_reg_field RxFifoWrInfoLn0_RxFifoWrLocEvnLn0;
	uvm_reg_field RxFifoWrLocEvnLn0;
	uvm_reg_field RxFifoWrInfoLn0_RxFifoWrLocOddLn0;
	uvm_reg_field RxFifoWrLocOddLn0;
	uvm_reg_field RxFifoWrInfoLn1_RxFifoWrLocEvnLn1;
	uvm_reg_field RxFifoWrLocEvnLn1;
	uvm_reg_field RxFifoWrInfoLn1_RxFifoWrLocOddLn1;
	uvm_reg_field RxFifoWrLocOddLn1;
	uvm_reg_field RxFifoWrInfoLn2_RxFifoWrLocEvnLn2;
	uvm_reg_field RxFifoWrLocEvnLn2;
	uvm_reg_field RxFifoWrInfoLn2_RxFifoWrLocOddLn2;
	uvm_reg_field RxFifoWrLocOddLn2;
	uvm_reg_field RxFifoWrInfoLn3_RxFifoWrLocEvnLn3;
	uvm_reg_field RxFifoWrLocEvnLn3;
	uvm_reg_field RxFifoWrInfoLn3_RxFifoWrLocOddLn3;
	uvm_reg_field RxFifoWrLocOddLn3;
	uvm_reg_field RxFifoRdInfoLn0_RxFifoRdLocLn0;
	uvm_reg_field RxFifoRdLocLn0;
	uvm_reg_field RxFifoRdInfoLn1_RxFifoRdLocLn1;
	uvm_reg_field RxFifoRdLocLn1;
	uvm_reg_field RxFifoRdInfoLn2_RxFifoRdLocLn2;
	uvm_reg_field RxFifoRdLocLn2;
	uvm_reg_field RxFifoRdInfoLn3_RxFifoRdLocLn3;
	uvm_reg_field RxFifoRdLocLn3;
	rand uvm_reg_field PclkDCAStatusSel_PclkDCADebugLaneSel;
	rand uvm_reg_field PclkDCADebugLaneSel;
	rand uvm_reg_field PclkDCAStatusSel_PclkDCADebugInfoSel;
	rand uvm_reg_field PclkDCADebugInfoSel;
	uvm_reg_field PclkDCAStatusInfo_PclkDCAStatusInfo;
	rand uvm_reg_field TxDcaCtrlTTg0_p0_TxDcaFinePDTTg0;
	rand uvm_reg_field TxDcaFinePDTTg0;
	rand uvm_reg_field TxDcaCtrlTTg0_p0_TxDcaFinePUTTg0;
	rand uvm_reg_field TxDcaFinePUTTg0;
	rand uvm_reg_field TxDcaCtrlTTg0_p0_TxDcaCoarseTTg0;
	rand uvm_reg_field TxDcaCoarseTTg0;
	rand uvm_reg_field TxDcaCtrlTTg1_p0_TxDcaFinePDTTg1;
	rand uvm_reg_field TxDcaFinePDTTg1;
	rand uvm_reg_field TxDcaCtrlTTg1_p0_TxDcaFinePUTTg1;
	rand uvm_reg_field TxDcaFinePUTTg1;
	rand uvm_reg_field TxDcaCtrlTTg1_p0_TxDcaCoarseTTg1;
	rand uvm_reg_field TxDcaCoarseTTg1;
	rand uvm_reg_field TxDcaCtrlCTg0_p0_TxDcaFinePDCTg0;
	rand uvm_reg_field TxDcaFinePDCTg0;
	rand uvm_reg_field TxDcaCtrlCTg0_p0_TxDcaFinePUCTg0;
	rand uvm_reg_field TxDcaFinePUCTg0;
	rand uvm_reg_field TxDcaCtrlCTg0_p0_TxDcaCoarseCTg0;
	rand uvm_reg_field TxDcaCoarseCTg0;
	rand uvm_reg_field TxDcaCtrlCTg1_p0_TxDcaFinePDCTg1;
	rand uvm_reg_field TxDcaFinePDCTg1;
	rand uvm_reg_field TxDcaCtrlCTg1_p0_TxDcaFinePUCTg1;
	rand uvm_reg_field TxDcaFinePUCTg1;
	rand uvm_reg_field TxDcaCtrlCTg1_p0_TxDcaCoarseCTg1;
	rand uvm_reg_field TxDcaCoarseCTg1;
	rand uvm_reg_field RxDcaCtrlTTg0_p0_RxDcaFinePDTTg0;
	rand uvm_reg_field RxDcaFinePDTTg0;
	rand uvm_reg_field RxDcaCtrlTTg0_p0_RxDcaFinePUTTg0;
	rand uvm_reg_field RxDcaFinePUTTg0;
	rand uvm_reg_field RxDcaCtrlTTg0_p0_RxDcaCoarseTTg0;
	rand uvm_reg_field RxDcaCoarseTTg0;
	rand uvm_reg_field RxDcaCtrlTTg1_p0_RxDcaFinePDTTg1;
	rand uvm_reg_field RxDcaFinePDTTg1;
	rand uvm_reg_field RxDcaCtrlTTg1_p0_RxDcaFinePUTTg1;
	rand uvm_reg_field RxDcaFinePUTTg1;
	rand uvm_reg_field RxDcaCtrlTTg1_p0_RxDcaCoarseTTg1;
	rand uvm_reg_field RxDcaCoarseTTg1;
	rand uvm_reg_field RxDcaCtrlCTg0_p0_RxDcaFinePDCTg0;
	rand uvm_reg_field RxDcaFinePDCTg0;
	rand uvm_reg_field RxDcaCtrlCTg0_p0_RxDcaFinePUCTg0;
	rand uvm_reg_field RxDcaFinePUCTg0;
	rand uvm_reg_field RxDcaCtrlCTg0_p0_RxDcaCoarseCTg0;
	rand uvm_reg_field RxDcaCoarseCTg0;
	rand uvm_reg_field RxDcaCtrlCTg1_p0_RxDcaFinePDCTg1;
	rand uvm_reg_field RxDcaFinePDCTg1;
	rand uvm_reg_field RxDcaCtrlCTg1_p0_RxDcaFinePUCTg1;
	rand uvm_reg_field RxDcaFinePUCTg1;
	rand uvm_reg_field RxDcaCtrlCTg1_p0_RxDcaCoarseCTg1;
	rand uvm_reg_field RxDcaCoarseCTg1;
	rand uvm_reg_field PclkDCALcdlCalCtrl_PclkDCAUseCSRForCalCtrl;
	rand uvm_reg_field PclkDCAUseCSRForCalCtrl;
	rand uvm_reg_field PclkDCALcdlCalCtrl_PclkDCALcdlCalMode;
	rand uvm_reg_field PclkDCALcdlCalMode;
	rand uvm_reg_field PclkDCALcdlCalCtrl_PclkDCALcdlCalEn;
	rand uvm_reg_field PclkDCALcdlCalEn;
	rand uvm_reg_field PclkDCALcdlCalCtrl_PclkDCALcdlCalPhaseUpdate;
	rand uvm_reg_field PclkDCALcdlCalPhaseUpdate;
	rand uvm_reg_field PclkDCALcdlCalCtrl_PclkDCALcdlCalClkEn;
	rand uvm_reg_field PclkDCALcdlCalClkEn;
	rand uvm_reg_field PclkDCALcdlCalCtrl_PclkDCALcdlCalSampEn;
	rand uvm_reg_field PclkDCALcdlCalSampEn;
	rand uvm_reg_field PclkDCALcdlCalCtrl_PclkDCALcdlResetRelock;
	rand uvm_reg_field PclkDCALcdlResetRelock;
	rand uvm_reg_field PclkDCALcdlCalCtrl_PclkDCALcdlStopCal;
	rand uvm_reg_field PclkDCALcdlStopCal;
	rand uvm_reg_field DlyTestCntDfiClkIVHM_DlyTestCntDfiClkIVHM;
	uvm_reg_field DlyTestCntDfiClkHM_DlyTestCntDfiClkHM;
	uvm_reg_field DlyTestCntRingOsc_DlyTestCntRingOsc;
	rand uvm_reg_field DlyTestSeqHM_DlyTestSeqHM;
	rand uvm_reg_field PclkDCALcdlAddDlySampEn_p0_PclkDCALcdlAddDlySampEn_p0;
	rand uvm_reg_field PclkEnDQSIO_PclkEnDQSIO;
	rand uvm_reg_field TxDcaCtrlTg0Ln0_p0_TxDcaCoarseTg0Ln0;
	rand uvm_reg_field TxDcaCoarseTg0Ln0;
	rand uvm_reg_field TxDcaCtrlTg0Ln0_p0_TxDcaFinePUTg0Ln0;
	rand uvm_reg_field TxDcaFinePUTg0Ln0;
	rand uvm_reg_field TxDcaCtrlTg0Ln0_p0_TxDcaFinePDTg0Ln0;
	rand uvm_reg_field TxDcaFinePDTg0Ln0;
	rand uvm_reg_field TxDcaCtrlTg1Ln0_p0_TxDcaCoarseTg1Ln0;
	rand uvm_reg_field TxDcaCoarseTg1Ln0;
	rand uvm_reg_field TxDcaCtrlTg1Ln0_p0_TxDcaFinePUTg1Ln0;
	rand uvm_reg_field TxDcaFinePUTg1Ln0;
	rand uvm_reg_field TxDcaCtrlTg1Ln0_p0_TxDcaFinePDTg1Ln0;
	rand uvm_reg_field TxDcaFinePDTg1Ln0;
	rand uvm_reg_field TxDcaCtrlTg0Ln1_p0_TxDcaCoarseTg0Ln1;
	rand uvm_reg_field TxDcaCoarseTg0Ln1;
	rand uvm_reg_field TxDcaCtrlTg0Ln1_p0_TxDcaFinePUTg0Ln1;
	rand uvm_reg_field TxDcaFinePUTg0Ln1;
	rand uvm_reg_field TxDcaCtrlTg0Ln1_p0_TxDcaFinePDTg0Ln1;
	rand uvm_reg_field TxDcaFinePDTg0Ln1;
	rand uvm_reg_field TxDcaCtrlTg1Ln1_p0_TxDcaCoarseTg1Ln1;
	rand uvm_reg_field TxDcaCoarseTg1Ln1;
	rand uvm_reg_field TxDcaCtrlTg1Ln1_p0_TxDcaFinePUTg1Ln1;
	rand uvm_reg_field TxDcaFinePUTg1Ln1;
	rand uvm_reg_field TxDcaCtrlTg1Ln1_p0_TxDcaFinePDTg1Ln1;
	rand uvm_reg_field TxDcaFinePDTg1Ln1;
	rand uvm_reg_field TxDcaCtrlTg0Ln2_p0_TxDcaCoarseTg0Ln2;
	rand uvm_reg_field TxDcaCoarseTg0Ln2;
	rand uvm_reg_field TxDcaCtrlTg0Ln2_p0_TxDcaFinePUTg0Ln2;
	rand uvm_reg_field TxDcaFinePUTg0Ln2;
	rand uvm_reg_field TxDcaCtrlTg0Ln2_p0_TxDcaFinePDTg0Ln2;
	rand uvm_reg_field TxDcaFinePDTg0Ln2;
	rand uvm_reg_field TxDcaCtrlTg1Ln2_p0_TxDcaCoarseTg1Ln2;
	rand uvm_reg_field TxDcaCoarseTg1Ln2;
	rand uvm_reg_field TxDcaCtrlTg1Ln2_p0_TxDcaFinePUTg1Ln2;
	rand uvm_reg_field TxDcaFinePUTg1Ln2;
	rand uvm_reg_field TxDcaCtrlTg1Ln2_p0_TxDcaFinePDTg1Ln2;
	rand uvm_reg_field TxDcaFinePDTg1Ln2;
	rand uvm_reg_field TxDcaCtrlTg0Ln3_p0_TxDcaCoarseTg0Ln3;
	rand uvm_reg_field TxDcaCoarseTg0Ln3;
	rand uvm_reg_field TxDcaCtrlTg0Ln3_p0_TxDcaFinePUTg0Ln3;
	rand uvm_reg_field TxDcaFinePUTg0Ln3;
	rand uvm_reg_field TxDcaCtrlTg0Ln3_p0_TxDcaFinePDTg0Ln3;
	rand uvm_reg_field TxDcaFinePDTg0Ln3;
	rand uvm_reg_field TxDcaCtrlTg1Ln3_p0_TxDcaCoarseTg1Ln3;
	rand uvm_reg_field TxDcaCoarseTg1Ln3;
	rand uvm_reg_field TxDcaCtrlTg1Ln3_p0_TxDcaFinePUTg1Ln3;
	rand uvm_reg_field TxDcaFinePUTg1Ln3;
	rand uvm_reg_field TxDcaCtrlTg1Ln3_p0_TxDcaFinePDTg1Ln3;
	rand uvm_reg_field TxDcaFinePDTg1Ln3;
	uvm_reg_field RxReplicaLcdlStatus_RxReplicaLcdlFineSnapVal;
	uvm_reg_field RxReplicaLcdlFineSnapVal;
	rand uvm_reg_field DlyTestCntRingOscSelDX_DlyTestCntRingOscSelDX;
	rand uvm_reg_field DlyTestRingSelDX_DlyTestRingSelDX;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	RxDFECtrlDq_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2 };
		option.weight = 1;
	}

	RxCurrAdj : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4 };
		option.weight = 1;
	}

	LpDqPowerDnDly_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5 };
		option.weight = 1;
	}

	LpDqPowerDnEn : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h6 };
		option.weight = 1;
	}

	RdfPtrChkErrInject : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h8 };
		option.weight = 1;
	}

	DxDigStrobeMode_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB };
		option.weight = 1;
	}

	RxModeCtl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC };
		option.weight = 1;
	}

	RxMiscCtl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD };
		option.weight = 1;
	}

	DqVregRsvd : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h10 };
		option.weight = 1;
	}

	DqVregRsvdP_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h12 };
		option.weight = 1;
	}

	EnaRxStrobeEnB_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h13 };
		option.weight = 1;
	}

	MtestMuxSel : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1A };
		option.weight = 1;
	}

	TxDQSlew_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1C };
		option.weight = 1;
	}

	RxPowerDownLightEn : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h25 };
		option.weight = 1;
	}

	RxDFEBiasSelLn0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h26 };
		option.weight = 1;
	}

	RxDFEBiasSelLn1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h27 };
		option.weight = 1;
	}

	RxDFEBiasSelLn2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h28 };
		option.weight = 1;
	}

	RxDFEBiasSelLn3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h29 };
		option.weight = 1;
	}

	TxImpedanceDq_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2C };
		option.weight = 1;
	}

	TxImpedanceDqs_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2D };
		option.weight = 1;
	}

	OdtImpedanceDq_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2E };
		option.weight = 1;
	}

	OdtImpedanceDqs_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2F };
		option.weight = 1;
	}

	RxDQSSeVrefDAC0_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3C };
		option.weight = 1;
	}

	RxDQSCtrl_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3E };
		option.weight = 1;
	}

	TxDQDcaMode_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3F };
		option.weight = 1;
	}

	TxModeCtlDQLn0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h40 };
		option.weight = 1;
	}

	TxModeCtlDQLn1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h41 };
		option.weight = 1;
	}

	TxModeCtlDQLn2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h42 };
		option.weight = 1;
	}

	TxModeCtlDQLn3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h43 };
		option.weight = 1;
	}

	TxModeCtlDQS : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h45 };
		option.weight = 1;
	}

	DxRxPowerDownLn0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h46 };
		option.weight = 1;
	}

	DxRxPowerDownLn1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h47 };
		option.weight = 1;
	}

	DxRxPowerDownLn2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h48 };
		option.weight = 1;
	}

	DxRxPowerDownLn3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h49 };
		option.weight = 1;
	}

	DxRxPowerDownDQS : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4B };
		option.weight = 1;
	}

	HMDBYTEParityInvert : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4D };
		option.weight = 1;
	}

	HMLcdlStatusSel : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h61 };
		option.weight = 1;
	}

	HMLcdlStatus : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h62 };
		option.weight = 1;
	}

	HMTxLcdlSeed_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h63 };
		option.weight = 1;
	}

	HMRxLcdlSeed_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h64 };
		option.weight = 1;
	}

	HMDBYTELcdlCalDeltaStepEn : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h65 };
		option.weight = 1;
	}

	LcdlMonitorCtl_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h66 };
		option.weight = 1;
	}

	HMDBYTELcdlCalDeltaMM_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h67 };
		option.weight = 1;
	}

	RxOffsetSelEvenSLn0_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h70 };
		option.weight = 1;
	}

	RxOffsetSelEvenSLn1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h71 };
		option.weight = 1;
	}

	RxOffsetSelEvenSLn2_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h72 };
		option.weight = 1;
	}

	RxOffsetSelEvenSLn3_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h73 };
		option.weight = 1;
	}

	RxOffsetSelOddSLn0_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h75 };
		option.weight = 1;
	}

	RxOffsetSelOddSLn1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h76 };
		option.weight = 1;
	}

	RxOffsetSelOddSLn2_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h77 };
		option.weight = 1;
	}

	RxOffsetSelOddSLn3_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h78 };
		option.weight = 1;
	}

	RxModeX8Sel : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h7A };
		option.weight = 1;
	}

	ScratchPadHMDBYTE : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h7D };
		option.weight = 1;
	}

	LcdlTstPhase : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h84 };
		option.weight = 1;
	}

	HMRxReplicaLcdlSeed_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h87 };
		option.weight = 1;
	}

	TxDiffDcaMode_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h8D };
		option.weight = 1;
	}

	DxCoreLoopBackMode : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h91 };
		option.weight = 1;
	}

	RxDFETap1SelTg0Ln0_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA0 };
		option.weight = 1;
	}

	RxDFETap1SelTg1Ln0_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA1 };
		option.weight = 1;
	}

	RxDFETap2SelTg0Ln0_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA4 };
		option.weight = 1;
	}

	RxDFETap2SelTg1Ln0_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA5 };
		option.weight = 1;
	}

	RxDFETap1SelTg0Ln1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB0 };
		option.weight = 1;
	}

	RxDFETap1SelTg1Ln1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB1 };
		option.weight = 1;
	}

	RxDFETap2SelTg0Ln1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB4 };
		option.weight = 1;
	}

	RxDFETap2SelTg1Ln1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB5 };
		option.weight = 1;
	}

	RxDFETap1SelTg0Ln2_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC0 };
		option.weight = 1;
	}

	RxDFETap1SelTg1Ln2_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC1 };
		option.weight = 1;
	}

	RxDFETap2SelTg0Ln2_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC4 };
		option.weight = 1;
	}

	RxDFETap2SelTg1Ln2_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC5 };
		option.weight = 1;
	}

	RxDFETap1SelTg0Ln3_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD0 };
		option.weight = 1;
	}

	RxDFETap1SelTg1Ln3_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD1 };
		option.weight = 1;
	}

	RxDFETap2SelTg0Ln3_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD4 };
		option.weight = 1;
	}

	RxDFETap2SelTg1Ln3_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD5 };
		option.weight = 1;
	}

	PclkDCACodeDqLn0_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF0 };
		option.weight = 1;
	}

	PclkDCACodeDqLn1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF1 };
		option.weight = 1;
	}

	PclkDCACodeDqLn2_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF2 };
		option.weight = 1;
	}

	PclkDCACodeDqLn3_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF3 };
		option.weight = 1;
	}

	PclkDCACodeDQS_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF5 };
		option.weight = 1;
	}

	HardMacroModeSel : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF6 };
		option.weight = 1;
	}

	TxFuncMode : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF8 };
		option.weight = 1;
	}

	HMReserved0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFE };
		option.weight = 1;
	}

	HMReservedP1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFF };
		option.weight = 1;
	}

	PclkDCATxLcdlPhase_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h110 };
		option.weight = 1;
	}

	RxReplicaLcdlDbgCntl2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h185 };
		option.weight = 1;
	}

	RxReplicaLcdlCalPhase : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h188 };
		option.weight = 1;
	}

	PclkDCDOffsetDqLn0_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h200 };
		option.weight = 1;
	}

	PclkDCDOffsetDqLn1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h201 };
		option.weight = 1;
	}

	PclkDCDOffsetDqLn2_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h202 };
		option.weight = 1;
	}

	PclkDCDOffsetDqLn3_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h203 };
		option.weight = 1;
	}

	PclkDCDOffsetDQS_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h205 };
		option.weight = 1;
	}

	PclkDCACalSampDqLn0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h300 };
		option.weight = 1;
	}

	PclkDCACalSampDqLn1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h301 };
		option.weight = 1;
	}

	PclkDCACalSampDqLn2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h302 };
		option.weight = 1;
	}

	PclkDCACalSampDqLn3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h303 };
		option.weight = 1;
	}

	PclkDCACalSampDQS : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h305 };
		option.weight = 1;
	}

	PclkDCAResults : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h30A };
		option.weight = 1;
	}

	RxFifoWrInfoLn0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h320 };
		option.weight = 1;
	}

	RxFifoWrInfoLn1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h321 };
		option.weight = 1;
	}

	RxFifoWrInfoLn2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h322 };
		option.weight = 1;
	}

	RxFifoWrInfoLn3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h323 };
		option.weight = 1;
	}

	RxFifoRdInfoLn0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h328 };
		option.weight = 1;
	}

	RxFifoRdInfoLn1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h329 };
		option.weight = 1;
	}

	RxFifoRdInfoLn2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h32A };
		option.weight = 1;
	}

	RxFifoRdInfoLn3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h32B };
		option.weight = 1;
	}

	PclkDCAStatusSel : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h511 };
		option.weight = 1;
	}

	PclkDCAStatusInfo : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h512 };
		option.weight = 1;
	}

	TxDcaCtrlTTg0_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h550 };
		option.weight = 1;
	}

	TxDcaCtrlTTg1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h551 };
		option.weight = 1;
	}

	TxDcaCtrlCTg0_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h560 };
		option.weight = 1;
	}

	TxDcaCtrlCTg1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h561 };
		option.weight = 1;
	}

	RxDcaCtrlTTg0_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h570 };
		option.weight = 1;
	}

	RxDcaCtrlTTg1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h571 };
		option.weight = 1;
	}

	RxDcaCtrlCTg0_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h580 };
		option.weight = 1;
	}

	RxDcaCtrlCTg1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h581 };
		option.weight = 1;
	}

	PclkDCALcdlCalCtrl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h591 };
		option.weight = 1;
	}

	DlyTestCntDfiClkIVHM : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5D3 };
		option.weight = 1;
	}

	DlyTestCntDfiClkHM : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5D4 };
		option.weight = 1;
	}

	DlyTestCntRingOsc : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5D5 };
		option.weight = 1;
	}

	DlyTestSeqHM : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5DF };
		option.weight = 1;
	}

	PclkDCALcdlAddDlySampEn_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5E3 };
		option.weight = 1;
	}

	PclkEnDQSIO : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5E4 };
		option.weight = 1;
	}

	TxDcaCtrlTg0Ln0_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h600 };
		option.weight = 1;
	}

	TxDcaCtrlTg1Ln0_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h601 };
		option.weight = 1;
	}

	TxDcaCtrlTg0Ln1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h610 };
		option.weight = 1;
	}

	TxDcaCtrlTg1Ln1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h611 };
		option.weight = 1;
	}

	TxDcaCtrlTg0Ln2_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h620 };
		option.weight = 1;
	}

	TxDcaCtrlTg1Ln2_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h621 };
		option.weight = 1;
	}

	TxDcaCtrlTg0Ln3_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h630 };
		option.weight = 1;
	}

	TxDcaCtrlTg1Ln3_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h631 };
		option.weight = 1;
	}

	RxReplicaLcdlStatus : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h67C };
		option.weight = 1;
	}

	DlyTestCntRingOscSelDX : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h692 };
		option.weight = 1;
	}

	DlyTestRingSelDX : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h6D1 };
		option.weight = 1;
	}
endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_4_p0");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.RxDFECtrlDq_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFECtrlDq_p0::type_id::create("RxDFECtrlDq_p0",,get_full_name());
      if(this.RxDFECtrlDq_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDFECtrlDq_p0.cg_bits.option.name = {get_name(), ".", "RxDFECtrlDq_p0_bits"};
      this.RxDFECtrlDq_p0.configure(this, null, "");
      this.RxDFECtrlDq_p0.build();
      this.default_map.add_reg(this.RxDFECtrlDq_p0, `UVM_REG_ADDR_WIDTH'h2, "RW", 0);
		this.RxDFECtrlDq_p0_RxDFECtrlDq_p0 = this.RxDFECtrlDq_p0.RxDFECtrlDq_p0;
      this.RxCurrAdj = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxCurrAdj::type_id::create("RxCurrAdj",,get_full_name());
      if(this.RxCurrAdj.has_coverage(UVM_CVR_ALL))
      	this.RxCurrAdj.cg_bits.option.name = {get_name(), ".", "RxCurrAdj_bits"};
      this.RxCurrAdj.configure(this, null, "");
      this.RxCurrAdj.build();
      this.default_map.add_reg(this.RxCurrAdj, `UVM_REG_ADDR_WIDTH'h4, "RW", 0);
		this.RxCurrAdj_RxCurrAdj = this.RxCurrAdj.RxCurrAdj;
      this.LpDqPowerDnDly_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_LpDqPowerDnDly_p0::type_id::create("LpDqPowerDnDly_p0",,get_full_name());
      if(this.LpDqPowerDnDly_p0.has_coverage(UVM_CVR_ALL))
      	this.LpDqPowerDnDly_p0.cg_bits.option.name = {get_name(), ".", "LpDqPowerDnDly_p0_bits"};
      this.LpDqPowerDnDly_p0.configure(this, null, "");
      this.LpDqPowerDnDly_p0.build();
      this.default_map.add_reg(this.LpDqPowerDnDly_p0, `UVM_REG_ADDR_WIDTH'h5, "RW", 0);
		this.LpDqPowerDnDly_p0_LpDqPowerDnDly_p0 = this.LpDqPowerDnDly_p0.LpDqPowerDnDly_p0;
      this.LpDqPowerDnEn = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_LpDqPowerDnEn::type_id::create("LpDqPowerDnEn",,get_full_name());
      if(this.LpDqPowerDnEn.has_coverage(UVM_CVR_ALL))
      	this.LpDqPowerDnEn.cg_bits.option.name = {get_name(), ".", "LpDqPowerDnEn_bits"};
      this.LpDqPowerDnEn.configure(this, null, "");
      this.LpDqPowerDnEn.build();
      this.default_map.add_reg(this.LpDqPowerDnEn, `UVM_REG_ADDR_WIDTH'h6, "RW", 0);
		this.LpDqPowerDnEn_LpDqPowerDnEn = this.LpDqPowerDnEn.LpDqPowerDnEn;
      this.RdfPtrChkErrInject = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RdfPtrChkErrInject::type_id::create("RdfPtrChkErrInject",,get_full_name());
      if(this.RdfPtrChkErrInject.has_coverage(UVM_CVR_ALL))
      	this.RdfPtrChkErrInject.cg_bits.option.name = {get_name(), ".", "RdfPtrChkErrInject_bits"};
      this.RdfPtrChkErrInject.configure(this, null, "");
      this.RdfPtrChkErrInject.build();
      this.default_map.add_reg(this.RdfPtrChkErrInject, `UVM_REG_ADDR_WIDTH'h8, "RW", 0);
		this.RdfPtrChkErrInject_RdfPtrChkErrInject = this.RdfPtrChkErrInject.RdfPtrChkErrInject;
      this.DxDigStrobeMode_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxDigStrobeMode_p0::type_id::create("DxDigStrobeMode_p0",,get_full_name());
      if(this.DxDigStrobeMode_p0.has_coverage(UVM_CVR_ALL))
      	this.DxDigStrobeMode_p0.cg_bits.option.name = {get_name(), ".", "DxDigStrobeMode_p0_bits"};
      this.DxDigStrobeMode_p0.configure(this, null, "");
      this.DxDigStrobeMode_p0.build();
      this.default_map.add_reg(this.DxDigStrobeMode_p0, `UVM_REG_ADDR_WIDTH'hB, "RW", 0);
		this.DxDigStrobeMode_p0_DxDigStrobeMode_p0 = this.DxDigStrobeMode_p0.DxDigStrobeMode_p0;
      this.RxModeCtl = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxModeCtl::type_id::create("RxModeCtl",,get_full_name());
      if(this.RxModeCtl.has_coverage(UVM_CVR_ALL))
      	this.RxModeCtl.cg_bits.option.name = {get_name(), ".", "RxModeCtl_bits"};
      this.RxModeCtl.configure(this, null, "");
      this.RxModeCtl.build();
      this.default_map.add_reg(this.RxModeCtl, `UVM_REG_ADDR_WIDTH'hC, "RW", 0);
		this.RxModeCtl_RxModeCtl = this.RxModeCtl.RxModeCtl;
      this.RxMiscCtl = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxMiscCtl::type_id::create("RxMiscCtl",,get_full_name());
      if(this.RxMiscCtl.has_coverage(UVM_CVR_ALL))
      	this.RxMiscCtl.cg_bits.option.name = {get_name(), ".", "RxMiscCtl_bits"};
      this.RxMiscCtl.configure(this, null, "");
      this.RxMiscCtl.build();
      this.default_map.add_reg(this.RxMiscCtl, `UVM_REG_ADDR_WIDTH'hD, "RW", 0);
		this.RxMiscCtl_RxOffsetEn = this.RxMiscCtl.RxOffsetEn;
		this.RxOffsetEn = this.RxMiscCtl.RxOffsetEn;
		this.RxMiscCtl_RxGainCtrl = this.RxMiscCtl.RxGainCtrl;
		this.RxGainCtrl = this.RxMiscCtl.RxGainCtrl;
      this.DqVregRsvd = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DqVregRsvd::type_id::create("DqVregRsvd",,get_full_name());
      if(this.DqVregRsvd.has_coverage(UVM_CVR_ALL))
      	this.DqVregRsvd.cg_bits.option.name = {get_name(), ".", "DqVregRsvd_bits"};
      this.DqVregRsvd.configure(this, null, "");
      this.DqVregRsvd.build();
      this.default_map.add_reg(this.DqVregRsvd, `UVM_REG_ADDR_WIDTH'h10, "RW", 0);
		this.DqVregRsvd_DqVregRsvd = this.DqVregRsvd.DqVregRsvd;
      this.DqVregRsvdP_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DqVregRsvdP_p0::type_id::create("DqVregRsvdP_p0",,get_full_name());
      if(this.DqVregRsvdP_p0.has_coverage(UVM_CVR_ALL))
      	this.DqVregRsvdP_p0.cg_bits.option.name = {get_name(), ".", "DqVregRsvdP_p0_bits"};
      this.DqVregRsvdP_p0.configure(this, null, "");
      this.DqVregRsvdP_p0.build();
      this.default_map.add_reg(this.DqVregRsvdP_p0, `UVM_REG_ADDR_WIDTH'h12, "RW", 0);
		this.DqVregRsvdP_p0_DqVregRsvdP_p0 = this.DqVregRsvdP_p0.DqVregRsvdP_p0;
      this.EnaRxStrobeEnB_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_EnaRxStrobeEnB_p0::type_id::create("EnaRxStrobeEnB_p0",,get_full_name());
      if(this.EnaRxStrobeEnB_p0.has_coverage(UVM_CVR_ALL))
      	this.EnaRxStrobeEnB_p0.cg_bits.option.name = {get_name(), ".", "EnaRxStrobeEnB_p0_bits"};
      this.EnaRxStrobeEnB_p0.configure(this, null, "");
      this.EnaRxStrobeEnB_p0.build();
      this.default_map.add_reg(this.EnaRxStrobeEnB_p0, `UVM_REG_ADDR_WIDTH'h13, "RW", 0);
		this.EnaRxStrobeEnB_p0_EnaRxStrobeEnB_p0 = this.EnaRxStrobeEnB_p0.EnaRxStrobeEnB_p0;
      this.MtestMuxSel = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_MtestMuxSel::type_id::create("MtestMuxSel",,get_full_name());
      if(this.MtestMuxSel.has_coverage(UVM_CVR_ALL))
      	this.MtestMuxSel.cg_bits.option.name = {get_name(), ".", "MtestMuxSel_bits"};
      this.MtestMuxSel.configure(this, null, "");
      this.MtestMuxSel.build();
      this.default_map.add_reg(this.MtestMuxSel, `UVM_REG_ADDR_WIDTH'h1A, "RW", 0);
		this.MtestMuxSel_MtestMuxSel = this.MtestMuxSel.MtestMuxSel;
      this.TxDQSlew_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDQSlew_p0::type_id::create("TxDQSlew_p0",,get_full_name());
      if(this.TxDQSlew_p0.has_coverage(UVM_CVR_ALL))
      	this.TxDQSlew_p0.cg_bits.option.name = {get_name(), ".", "TxDQSlew_p0_bits"};
      this.TxDQSlew_p0.configure(this, null, "");
      this.TxDQSlew_p0.build();
      this.default_map.add_reg(this.TxDQSlew_p0, `UVM_REG_ADDR_WIDTH'h1C, "RW", 0);
		this.TxDQSlew_p0_TxDQSlewPU = this.TxDQSlew_p0.TxDQSlewPU;
		this.TxDQSlewPU = this.TxDQSlew_p0.TxDQSlewPU;
		this.TxDQSlew_p0_TxDQSlewPD = this.TxDQSlew_p0.TxDQSlewPD;
		this.TxDQSlewPD = this.TxDQSlew_p0.TxDQSlewPD;
      this.RxPowerDownLightEn = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxPowerDownLightEn::type_id::create("RxPowerDownLightEn",,get_full_name());
      if(this.RxPowerDownLightEn.has_coverage(UVM_CVR_ALL))
      	this.RxPowerDownLightEn.cg_bits.option.name = {get_name(), ".", "RxPowerDownLightEn_bits"};
      this.RxPowerDownLightEn.configure(this, null, "");
      this.RxPowerDownLightEn.build();
      this.default_map.add_reg(this.RxPowerDownLightEn, `UVM_REG_ADDR_WIDTH'h25, "RW", 0);
		this.RxPowerDownLightEn_RxPowerDownLightEn = this.RxPowerDownLightEn.RxPowerDownLightEn;
      this.RxDFEBiasSelLn0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn0::type_id::create("RxDFEBiasSelLn0",,get_full_name());
      if(this.RxDFEBiasSelLn0.has_coverage(UVM_CVR_ALL))
      	this.RxDFEBiasSelLn0.cg_bits.option.name = {get_name(), ".", "RxDFEBiasSelLn0_bits"};
      this.RxDFEBiasSelLn0.configure(this, null, "");
      this.RxDFEBiasSelLn0.build();
      this.default_map.add_reg(this.RxDFEBiasSelLn0, `UVM_REG_ADDR_WIDTH'h26, "RW", 0);
		this.RxDFEBiasSelLn0_RxDFEBiasSelLn0 = this.RxDFEBiasSelLn0.RxDFEBiasSelLn0;
      this.RxDFEBiasSelLn1 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn1::type_id::create("RxDFEBiasSelLn1",,get_full_name());
      if(this.RxDFEBiasSelLn1.has_coverage(UVM_CVR_ALL))
      	this.RxDFEBiasSelLn1.cg_bits.option.name = {get_name(), ".", "RxDFEBiasSelLn1_bits"};
      this.RxDFEBiasSelLn1.configure(this, null, "");
      this.RxDFEBiasSelLn1.build();
      this.default_map.add_reg(this.RxDFEBiasSelLn1, `UVM_REG_ADDR_WIDTH'h27, "RW", 0);
		this.RxDFEBiasSelLn1_RxDFEBiasSelLn1 = this.RxDFEBiasSelLn1.RxDFEBiasSelLn1;
      this.RxDFEBiasSelLn2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn2::type_id::create("RxDFEBiasSelLn2",,get_full_name());
      if(this.RxDFEBiasSelLn2.has_coverage(UVM_CVR_ALL))
      	this.RxDFEBiasSelLn2.cg_bits.option.name = {get_name(), ".", "RxDFEBiasSelLn2_bits"};
      this.RxDFEBiasSelLn2.configure(this, null, "");
      this.RxDFEBiasSelLn2.build();
      this.default_map.add_reg(this.RxDFEBiasSelLn2, `UVM_REG_ADDR_WIDTH'h28, "RW", 0);
		this.RxDFEBiasSelLn2_RxDFEBiasSelLn2 = this.RxDFEBiasSelLn2.RxDFEBiasSelLn2;
      this.RxDFEBiasSelLn3 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFEBiasSelLn3::type_id::create("RxDFEBiasSelLn3",,get_full_name());
      if(this.RxDFEBiasSelLn3.has_coverage(UVM_CVR_ALL))
      	this.RxDFEBiasSelLn3.cg_bits.option.name = {get_name(), ".", "RxDFEBiasSelLn3_bits"};
      this.RxDFEBiasSelLn3.configure(this, null, "");
      this.RxDFEBiasSelLn3.build();
      this.default_map.add_reg(this.RxDFEBiasSelLn3, `UVM_REG_ADDR_WIDTH'h29, "RW", 0);
		this.RxDFEBiasSelLn3_RxDFEBiasSelLn3 = this.RxDFEBiasSelLn3.RxDFEBiasSelLn3;
      this.TxImpedanceDq_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxImpedanceDq_p0::type_id::create("TxImpedanceDq_p0",,get_full_name());
      if(this.TxImpedanceDq_p0.has_coverage(UVM_CVR_ALL))
      	this.TxImpedanceDq_p0.cg_bits.option.name = {get_name(), ".", "TxImpedanceDq_p0_bits"};
      this.TxImpedanceDq_p0.configure(this, null, "");
      this.TxImpedanceDq_p0.build();
      this.default_map.add_reg(this.TxImpedanceDq_p0, `UVM_REG_ADDR_WIDTH'h2C, "RW", 0);
		this.TxImpedanceDq_p0_TxStrenCodeDqPU = this.TxImpedanceDq_p0.TxStrenCodeDqPU;
		this.TxStrenCodeDqPU = this.TxImpedanceDq_p0.TxStrenCodeDqPU;
		this.TxImpedanceDq_p0_TxStrenCodeDqPD = this.TxImpedanceDq_p0.TxStrenCodeDqPD;
		this.TxStrenCodeDqPD = this.TxImpedanceDq_p0.TxStrenCodeDqPD;
      this.TxImpedanceDqs_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxImpedanceDqs_p0::type_id::create("TxImpedanceDqs_p0",,get_full_name());
      if(this.TxImpedanceDqs_p0.has_coverage(UVM_CVR_ALL))
      	this.TxImpedanceDqs_p0.cg_bits.option.name = {get_name(), ".", "TxImpedanceDqs_p0_bits"};
      this.TxImpedanceDqs_p0.configure(this, null, "");
      this.TxImpedanceDqs_p0.build();
      this.default_map.add_reg(this.TxImpedanceDqs_p0, `UVM_REG_ADDR_WIDTH'h2D, "RW", 0);
		this.TxImpedanceDqs_p0_TxStrenCodeDqsPUT = this.TxImpedanceDqs_p0.TxStrenCodeDqsPUT;
		this.TxStrenCodeDqsPUT = this.TxImpedanceDqs_p0.TxStrenCodeDqsPUT;
		this.TxImpedanceDqs_p0_TxStrenCodeDqsPUC = this.TxImpedanceDqs_p0.TxStrenCodeDqsPUC;
		this.TxStrenCodeDqsPUC = this.TxImpedanceDqs_p0.TxStrenCodeDqsPUC;
		this.TxImpedanceDqs_p0_TxStrenCodeDqsPDT = this.TxImpedanceDqs_p0.TxStrenCodeDqsPDT;
		this.TxStrenCodeDqsPDT = this.TxImpedanceDqs_p0.TxStrenCodeDqsPDT;
		this.TxImpedanceDqs_p0_TxStrenCodeDqsPDC = this.TxImpedanceDqs_p0.TxStrenCodeDqsPDC;
		this.TxStrenCodeDqsPDC = this.TxImpedanceDqs_p0.TxStrenCodeDqsPDC;
      this.OdtImpedanceDq_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_OdtImpedanceDq_p0::type_id::create("OdtImpedanceDq_p0",,get_full_name());
      if(this.OdtImpedanceDq_p0.has_coverage(UVM_CVR_ALL))
      	this.OdtImpedanceDq_p0.cg_bits.option.name = {get_name(), ".", "OdtImpedanceDq_p0_bits"};
      this.OdtImpedanceDq_p0.configure(this, null, "");
      this.OdtImpedanceDq_p0.build();
      this.default_map.add_reg(this.OdtImpedanceDq_p0, `UVM_REG_ADDR_WIDTH'h2E, "RW", 0);
		this.OdtImpedanceDq_p0_OdtStrenCodeDqPU = this.OdtImpedanceDq_p0.OdtStrenCodeDqPU;
		this.OdtStrenCodeDqPU = this.OdtImpedanceDq_p0.OdtStrenCodeDqPU;
		this.OdtImpedanceDq_p0_OdtStrenCodeDqPD = this.OdtImpedanceDq_p0.OdtStrenCodeDqPD;
		this.OdtStrenCodeDqPD = this.OdtImpedanceDq_p0.OdtStrenCodeDqPD;
      this.OdtImpedanceDqs_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_OdtImpedanceDqs_p0::type_id::create("OdtImpedanceDqs_p0",,get_full_name());
      if(this.OdtImpedanceDqs_p0.has_coverage(UVM_CVR_ALL))
      	this.OdtImpedanceDqs_p0.cg_bits.option.name = {get_name(), ".", "OdtImpedanceDqs_p0_bits"};
      this.OdtImpedanceDqs_p0.configure(this, null, "");
      this.OdtImpedanceDqs_p0.build();
      this.default_map.add_reg(this.OdtImpedanceDqs_p0, `UVM_REG_ADDR_WIDTH'h2F, "RW", 0);
		this.OdtImpedanceDqs_p0_OdtStrenCodeDqsPUT = this.OdtImpedanceDqs_p0.OdtStrenCodeDqsPUT;
		this.OdtStrenCodeDqsPUT = this.OdtImpedanceDqs_p0.OdtStrenCodeDqsPUT;
		this.OdtImpedanceDqs_p0_OdtStrenCodeDqsPUC = this.OdtImpedanceDqs_p0.OdtStrenCodeDqsPUC;
		this.OdtStrenCodeDqsPUC = this.OdtImpedanceDqs_p0.OdtStrenCodeDqsPUC;
		this.OdtImpedanceDqs_p0_OdtStrenCodeDqsPDT = this.OdtImpedanceDqs_p0.OdtStrenCodeDqsPDT;
		this.OdtStrenCodeDqsPDT = this.OdtImpedanceDqs_p0.OdtStrenCodeDqsPDT;
		this.OdtImpedanceDqs_p0_OdtStrenCodeDqsPDC = this.OdtImpedanceDqs_p0.OdtStrenCodeDqsPDC;
		this.OdtStrenCodeDqsPDC = this.OdtImpedanceDqs_p0.OdtStrenCodeDqsPDC;
      this.RxDQSSeVrefDAC0_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDQSSeVrefDAC0_p0::type_id::create("RxDQSSeVrefDAC0_p0",,get_full_name());
      if(this.RxDQSSeVrefDAC0_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDQSSeVrefDAC0_p0.cg_bits.option.name = {get_name(), ".", "RxDQSSeVrefDAC0_p0_bits"};
      this.RxDQSSeVrefDAC0_p0.configure(this, null, "");
      this.RxDQSSeVrefDAC0_p0.build();
      this.default_map.add_reg(this.RxDQSSeVrefDAC0_p0, `UVM_REG_ADDR_WIDTH'h3C, "RW", 0);
		this.RxDQSSeVrefDAC0_p0_RxDQSSeVrefDAC0_p0 = this.RxDQSSeVrefDAC0_p0.RxDQSSeVrefDAC0_p0;
      this.RxDQSCtrl_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDQSCtrl_p0::type_id::create("RxDQSCtrl_p0",,get_full_name());
      if(this.RxDQSCtrl_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDQSCtrl_p0.cg_bits.option.name = {get_name(), ".", "RxDQSCtrl_p0_bits"};
      this.RxDQSCtrl_p0.configure(this, null, "");
      this.RxDQSCtrl_p0.build();
      this.default_map.add_reg(this.RxDQSCtrl_p0, `UVM_REG_ADDR_WIDTH'h3E, "RW", 0);
		this.RxDQSCtrl_p0_RxDQSDiffSeVrefDACEn = this.RxDQSCtrl_p0.RxDQSDiffSeVrefDACEn;
		this.RxDQSDiffSeVrefDACEn = this.RxDQSCtrl_p0.RxDQSDiffSeVrefDACEn;
		this.RxDQSCtrl_p0_RxDiffSeCtrl = this.RxDQSCtrl_p0.RxDiffSeCtrl;
		this.RxDiffSeCtrl = this.RxDQSCtrl_p0.RxDiffSeCtrl;
      this.TxDQDcaMode_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDQDcaMode_p0::type_id::create("TxDQDcaMode_p0",,get_full_name());
      if(this.TxDQDcaMode_p0.has_coverage(UVM_CVR_ALL))
      	this.TxDQDcaMode_p0.cg_bits.option.name = {get_name(), ".", "TxDQDcaMode_p0_bits"};
      this.TxDQDcaMode_p0.configure(this, null, "");
      this.TxDQDcaMode_p0.build();
      this.default_map.add_reg(this.TxDQDcaMode_p0, `UVM_REG_ADDR_WIDTH'h3F, "RW", 0);
		this.TxDQDcaMode_p0_TxDQDcaMode_p0 = this.TxDQDcaMode_p0.TxDQDcaMode_p0;
      this.TxModeCtlDQLn0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn0::type_id::create("TxModeCtlDQLn0",,get_full_name());
      if(this.TxModeCtlDQLn0.has_coverage(UVM_CVR_ALL))
      	this.TxModeCtlDQLn0.cg_bits.option.name = {get_name(), ".", "TxModeCtlDQLn0_bits"};
      this.TxModeCtlDQLn0.configure(this, null, "");
      this.TxModeCtlDQLn0.build();
      this.default_map.add_reg(this.TxModeCtlDQLn0, `UVM_REG_ADDR_WIDTH'h40, "RW", 0);
		this.TxModeCtlDQLn0_TxModeCtlDQLn0 = this.TxModeCtlDQLn0.TxModeCtlDQLn0;
      this.TxModeCtlDQLn1 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn1::type_id::create("TxModeCtlDQLn1",,get_full_name());
      if(this.TxModeCtlDQLn1.has_coverage(UVM_CVR_ALL))
      	this.TxModeCtlDQLn1.cg_bits.option.name = {get_name(), ".", "TxModeCtlDQLn1_bits"};
      this.TxModeCtlDQLn1.configure(this, null, "");
      this.TxModeCtlDQLn1.build();
      this.default_map.add_reg(this.TxModeCtlDQLn1, `UVM_REG_ADDR_WIDTH'h41, "RW", 0);
		this.TxModeCtlDQLn1_TxModeCtlDQLn1 = this.TxModeCtlDQLn1.TxModeCtlDQLn1;
      this.TxModeCtlDQLn2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn2::type_id::create("TxModeCtlDQLn2",,get_full_name());
      if(this.TxModeCtlDQLn2.has_coverage(UVM_CVR_ALL))
      	this.TxModeCtlDQLn2.cg_bits.option.name = {get_name(), ".", "TxModeCtlDQLn2_bits"};
      this.TxModeCtlDQLn2.configure(this, null, "");
      this.TxModeCtlDQLn2.build();
      this.default_map.add_reg(this.TxModeCtlDQLn2, `UVM_REG_ADDR_WIDTH'h42, "RW", 0);
		this.TxModeCtlDQLn2_TxModeCtlDQLn2 = this.TxModeCtlDQLn2.TxModeCtlDQLn2;
      this.TxModeCtlDQLn3 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQLn3::type_id::create("TxModeCtlDQLn3",,get_full_name());
      if(this.TxModeCtlDQLn3.has_coverage(UVM_CVR_ALL))
      	this.TxModeCtlDQLn3.cg_bits.option.name = {get_name(), ".", "TxModeCtlDQLn3_bits"};
      this.TxModeCtlDQLn3.configure(this, null, "");
      this.TxModeCtlDQLn3.build();
      this.default_map.add_reg(this.TxModeCtlDQLn3, `UVM_REG_ADDR_WIDTH'h43, "RW", 0);
		this.TxModeCtlDQLn3_TxModeCtlDQLn3 = this.TxModeCtlDQLn3.TxModeCtlDQLn3;
      this.TxModeCtlDQS = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxModeCtlDQS::type_id::create("TxModeCtlDQS",,get_full_name());
      if(this.TxModeCtlDQS.has_coverage(UVM_CVR_ALL))
      	this.TxModeCtlDQS.cg_bits.option.name = {get_name(), ".", "TxModeCtlDQS_bits"};
      this.TxModeCtlDQS.configure(this, null, "");
      this.TxModeCtlDQS.build();
      this.default_map.add_reg(this.TxModeCtlDQS, `UVM_REG_ADDR_WIDTH'h45, "RW", 0);
		this.TxModeCtlDQS_TxModeCtlDQS = this.TxModeCtlDQS.TxModeCtlDQS;
      this.DxRxPowerDownLn0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn0::type_id::create("DxRxPowerDownLn0",,get_full_name());
      if(this.DxRxPowerDownLn0.has_coverage(UVM_CVR_ALL))
      	this.DxRxPowerDownLn0.cg_bits.option.name = {get_name(), ".", "DxRxPowerDownLn0_bits"};
      this.DxRxPowerDownLn0.configure(this, null, "");
      this.DxRxPowerDownLn0.build();
      this.default_map.add_reg(this.DxRxPowerDownLn0, `UVM_REG_ADDR_WIDTH'h46, "RW", 0);
		this.DxRxPowerDownLn0_TxPowerDownLn0 = this.DxRxPowerDownLn0.TxPowerDownLn0;
		this.TxPowerDownLn0 = this.DxRxPowerDownLn0.TxPowerDownLn0;
		this.DxRxPowerDownLn0_RxPowerDownLn0 = this.DxRxPowerDownLn0.RxPowerDownLn0;
		this.RxPowerDownLn0 = this.DxRxPowerDownLn0.RxPowerDownLn0;
      this.DxRxPowerDownLn1 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn1::type_id::create("DxRxPowerDownLn1",,get_full_name());
      if(this.DxRxPowerDownLn1.has_coverage(UVM_CVR_ALL))
      	this.DxRxPowerDownLn1.cg_bits.option.name = {get_name(), ".", "DxRxPowerDownLn1_bits"};
      this.DxRxPowerDownLn1.configure(this, null, "");
      this.DxRxPowerDownLn1.build();
      this.default_map.add_reg(this.DxRxPowerDownLn1, `UVM_REG_ADDR_WIDTH'h47, "RW", 0);
		this.DxRxPowerDownLn1_TxPowerDownLn1 = this.DxRxPowerDownLn1.TxPowerDownLn1;
		this.TxPowerDownLn1 = this.DxRxPowerDownLn1.TxPowerDownLn1;
		this.DxRxPowerDownLn1_RxPowerDownLn1 = this.DxRxPowerDownLn1.RxPowerDownLn1;
		this.RxPowerDownLn1 = this.DxRxPowerDownLn1.RxPowerDownLn1;
      this.DxRxPowerDownLn2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn2::type_id::create("DxRxPowerDownLn2",,get_full_name());
      if(this.DxRxPowerDownLn2.has_coverage(UVM_CVR_ALL))
      	this.DxRxPowerDownLn2.cg_bits.option.name = {get_name(), ".", "DxRxPowerDownLn2_bits"};
      this.DxRxPowerDownLn2.configure(this, null, "");
      this.DxRxPowerDownLn2.build();
      this.default_map.add_reg(this.DxRxPowerDownLn2, `UVM_REG_ADDR_WIDTH'h48, "RW", 0);
		this.DxRxPowerDownLn2_TxPowerDownLn2 = this.DxRxPowerDownLn2.TxPowerDownLn2;
		this.TxPowerDownLn2 = this.DxRxPowerDownLn2.TxPowerDownLn2;
		this.DxRxPowerDownLn2_RxPowerDownLn2 = this.DxRxPowerDownLn2.RxPowerDownLn2;
		this.RxPowerDownLn2 = this.DxRxPowerDownLn2.RxPowerDownLn2;
      this.DxRxPowerDownLn3 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownLn3::type_id::create("DxRxPowerDownLn3",,get_full_name());
      if(this.DxRxPowerDownLn3.has_coverage(UVM_CVR_ALL))
      	this.DxRxPowerDownLn3.cg_bits.option.name = {get_name(), ".", "DxRxPowerDownLn3_bits"};
      this.DxRxPowerDownLn3.configure(this, null, "");
      this.DxRxPowerDownLn3.build();
      this.default_map.add_reg(this.DxRxPowerDownLn3, `UVM_REG_ADDR_WIDTH'h49, "RW", 0);
		this.DxRxPowerDownLn3_TxPowerDownLn3 = this.DxRxPowerDownLn3.TxPowerDownLn3;
		this.TxPowerDownLn3 = this.DxRxPowerDownLn3.TxPowerDownLn3;
		this.DxRxPowerDownLn3_RxPowerDownLn3 = this.DxRxPowerDownLn3.RxPowerDownLn3;
		this.RxPowerDownLn3 = this.DxRxPowerDownLn3.RxPowerDownLn3;
      this.DxRxPowerDownDQS = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxRxPowerDownDQS::type_id::create("DxRxPowerDownDQS",,get_full_name());
      if(this.DxRxPowerDownDQS.has_coverage(UVM_CVR_ALL))
      	this.DxRxPowerDownDQS.cg_bits.option.name = {get_name(), ".", "DxRxPowerDownDQS_bits"};
      this.DxRxPowerDownDQS.configure(this, null, "");
      this.DxRxPowerDownDQS.build();
      this.default_map.add_reg(this.DxRxPowerDownDQS, `UVM_REG_ADDR_WIDTH'h4B, "RW", 0);
		this.DxRxPowerDownDQS_TxPowerDownDQS = this.DxRxPowerDownDQS.TxPowerDownDQS;
		this.TxPowerDownDQS = this.DxRxPowerDownDQS.TxPowerDownDQS;
		this.DxRxPowerDownDQS_RxPowerDownDQS = this.DxRxPowerDownDQS.RxPowerDownDQS;
		this.RxPowerDownDQS = this.DxRxPowerDownDQS.RxPowerDownDQS;
      this.HMDBYTEParityInvert = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMDBYTEParityInvert::type_id::create("HMDBYTEParityInvert",,get_full_name());
      if(this.HMDBYTEParityInvert.has_coverage(UVM_CVR_ALL))
      	this.HMDBYTEParityInvert.cg_bits.option.name = {get_name(), ".", "HMDBYTEParityInvert_bits"};
      this.HMDBYTEParityInvert.configure(this, null, "");
      this.HMDBYTEParityInvert.build();
      this.default_map.add_reg(this.HMDBYTEParityInvert, `UVM_REG_ADDR_WIDTH'h4D, "RW", 0);
		this.HMDBYTEParityInvert_HMDBYTEParityInvert = this.HMDBYTEParityInvert.HMDBYTEParityInvert;
      this.HMLcdlStatusSel = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMLcdlStatusSel::type_id::create("HMLcdlStatusSel",,get_full_name());
      if(this.HMLcdlStatusSel.has_coverage(UVM_CVR_ALL))
      	this.HMLcdlStatusSel.cg_bits.option.name = {get_name(), ".", "HMLcdlStatusSel_bits"};
      this.HMLcdlStatusSel.configure(this, null, "");
      this.HMLcdlStatusSel.build();
      this.default_map.add_reg(this.HMLcdlStatusSel, `UVM_REG_ADDR_WIDTH'h61, "RW", 0);
		this.HMLcdlStatusSel_HMLcdlSttsSelReg = this.HMLcdlStatusSel.HMLcdlSttsSelReg;
		this.HMLcdlSttsSelReg = this.HMLcdlStatusSel.HMLcdlSttsSelReg;
		this.HMLcdlStatusSel_HMLcdlSttsSelLane = this.HMLcdlStatusSel.HMLcdlSttsSelLane;
		this.HMLcdlSttsSelLane = this.HMLcdlStatusSel.HMLcdlSttsSelLane;
		this.HMLcdlStatusSel_HMBypMode = this.HMLcdlStatusSel.HMBypMode;
		this.HMBypMode = this.HMLcdlStatusSel.HMBypMode;
		this.HMLcdlStatusSel_HMDQSBypMode = this.HMLcdlStatusSel.HMDQSBypMode;
		this.HMDQSBypMode = this.HMLcdlStatusSel.HMDQSBypMode;
      this.HMLcdlStatus = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMLcdlStatus::type_id::create("HMLcdlStatus",,get_full_name());
      if(this.HMLcdlStatus.has_coverage(UVM_CVR_ALL))
      	this.HMLcdlStatus.cg_bits.option.name = {get_name(), ".", "HMLcdlStatus_bits"};
      this.HMLcdlStatus.configure(this, null, "");
      this.HMLcdlStatus.build();
      this.default_map.add_reg(this.HMLcdlStatus, `UVM_REG_ADDR_WIDTH'h62, "RO", 0);
		this.HMLcdlStatus_LcdlPhaseCal = this.HMLcdlStatus.LcdlPhaseCal;
		this.LcdlPhaseCal = this.HMLcdlStatus.LcdlPhaseCal;
		this.HMLcdlStatus_LcdlStatus09 = this.HMLcdlStatus.LcdlStatus09;
		this.LcdlStatus09 = this.HMLcdlStatus.LcdlStatus09;
		this.HMLcdlStatus_TstLiveLock = this.HMLcdlStatus.TstLiveLock;
		this.TstLiveLock = this.HMLcdlStatus.TstLiveLock;
		this.HMLcdlStatus_StickyUnlock = this.HMLcdlStatus.StickyUnlock;
		this.StickyUnlock = this.HMLcdlStatus.StickyUnlock;
		this.HMLcdlStatus_StickyLock = this.HMLcdlStatus.StickyLock;
		this.StickyLock = this.HMLcdlStatus.StickyLock;
		this.HMLcdlStatus_LcdlStatus15 = this.HMLcdlStatus.LcdlStatus15;
		this.LcdlStatus15 = this.HMLcdlStatus.LcdlStatus15;
      this.HMTxLcdlSeed_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMTxLcdlSeed_p0::type_id::create("HMTxLcdlSeed_p0",,get_full_name());
      if(this.HMTxLcdlSeed_p0.has_coverage(UVM_CVR_ALL))
      	this.HMTxLcdlSeed_p0.cg_bits.option.name = {get_name(), ".", "HMTxLcdlSeed_p0_bits"};
      this.HMTxLcdlSeed_p0.configure(this, null, "");
      this.HMTxLcdlSeed_p0.build();
      this.default_map.add_reg(this.HMTxLcdlSeed_p0, `UVM_REG_ADDR_WIDTH'h63, "RW", 0);
		this.HMTxLcdlSeed_p0_HMTxLcdlSeed_p0 = this.HMTxLcdlSeed_p0.HMTxLcdlSeed_p0;
      this.HMRxLcdlSeed_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMRxLcdlSeed_p0::type_id::create("HMRxLcdlSeed_p0",,get_full_name());
      if(this.HMRxLcdlSeed_p0.has_coverage(UVM_CVR_ALL))
      	this.HMRxLcdlSeed_p0.cg_bits.option.name = {get_name(), ".", "HMRxLcdlSeed_p0_bits"};
      this.HMRxLcdlSeed_p0.configure(this, null, "");
      this.HMRxLcdlSeed_p0.build();
      this.default_map.add_reg(this.HMRxLcdlSeed_p0, `UVM_REG_ADDR_WIDTH'h64, "RW", 0);
		this.HMRxLcdlSeed_p0_HMRxLcdlSeed_p0 = this.HMRxLcdlSeed_p0.HMRxLcdlSeed_p0;
      this.HMDBYTELcdlCalDeltaStepEn = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMDBYTELcdlCalDeltaStepEn::type_id::create("HMDBYTELcdlCalDeltaStepEn",,get_full_name());
      if(this.HMDBYTELcdlCalDeltaStepEn.has_coverage(UVM_CVR_ALL))
      	this.HMDBYTELcdlCalDeltaStepEn.cg_bits.option.name = {get_name(), ".", "HMDBYTELcdlCalDeltaStepEn_bits"};
      this.HMDBYTELcdlCalDeltaStepEn.configure(this, null, "");
      this.HMDBYTELcdlCalDeltaStepEn.build();
      this.default_map.add_reg(this.HMDBYTELcdlCalDeltaStepEn, `UVM_REG_ADDR_WIDTH'h65, "RW", 0);
		this.HMDBYTELcdlCalDeltaStepEn_TxLcdlCalDeltaStepEn = this.HMDBYTELcdlCalDeltaStepEn.TxLcdlCalDeltaStepEn;
		this.TxLcdlCalDeltaStepEn = this.HMDBYTELcdlCalDeltaStepEn.TxLcdlCalDeltaStepEn;
		this.HMDBYTELcdlCalDeltaStepEn_RxLcdlCalDeltaStepEn = this.HMDBYTELcdlCalDeltaStepEn.RxLcdlCalDeltaStepEn;
		this.RxLcdlCalDeltaStepEn = this.HMDBYTELcdlCalDeltaStepEn.RxLcdlCalDeltaStepEn;
		this.HMDBYTELcdlCalDeltaStepEn_RxReplicaLcdlCalDeltaStepEn = this.HMDBYTELcdlCalDeltaStepEn.RxReplicaLcdlCalDeltaStepEn;
		this.RxReplicaLcdlCalDeltaStepEn = this.HMDBYTELcdlCalDeltaStepEn.RxReplicaLcdlCalDeltaStepEn;
      this.LcdlMonitorCtl_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_LcdlMonitorCtl_p0::type_id::create("LcdlMonitorCtl_p0",,get_full_name());
      if(this.LcdlMonitorCtl_p0.has_coverage(UVM_CVR_ALL))
      	this.LcdlMonitorCtl_p0.cg_bits.option.name = {get_name(), ".", "LcdlMonitorCtl_p0_bits"};
      this.LcdlMonitorCtl_p0.configure(this, null, "");
      this.LcdlMonitorCtl_p0.build();
      this.default_map.add_reg(this.LcdlMonitorCtl_p0, `UVM_REG_ADDR_WIDTH'h66, "RW", 0);
		this.LcdlMonitorCtl_p0_StickyUnlckThrshld = this.LcdlMonitorCtl_p0.StickyUnlckThrshld;
		this.StickyUnlckThrshld = this.LcdlMonitorCtl_p0.StickyUnlckThrshld;
      this.HMDBYTELcdlCalDeltaMM_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMDBYTELcdlCalDeltaMM_p0::type_id::create("HMDBYTELcdlCalDeltaMM_p0",,get_full_name());
      if(this.HMDBYTELcdlCalDeltaMM_p0.has_coverage(UVM_CVR_ALL))
      	this.HMDBYTELcdlCalDeltaMM_p0.cg_bits.option.name = {get_name(), ".", "HMDBYTELcdlCalDeltaMM_p0_bits"};
      this.HMDBYTELcdlCalDeltaMM_p0.configure(this, null, "");
      this.HMDBYTELcdlCalDeltaMM_p0.build();
      this.default_map.add_reg(this.HMDBYTELcdlCalDeltaMM_p0, `UVM_REG_ADDR_WIDTH'h67, "RW", 0);
		this.HMDBYTELcdlCalDeltaMM_p0_TxLcdlCalDeltaMM = this.HMDBYTELcdlCalDeltaMM_p0.TxLcdlCalDeltaMM;
		this.TxLcdlCalDeltaMM = this.HMDBYTELcdlCalDeltaMM_p0.TxLcdlCalDeltaMM;
		this.HMDBYTELcdlCalDeltaMM_p0_RxLcdlCalDeltaMM = this.HMDBYTELcdlCalDeltaMM_p0.RxLcdlCalDeltaMM;
		this.RxLcdlCalDeltaMM = this.HMDBYTELcdlCalDeltaMM_p0.RxLcdlCalDeltaMM;
		this.HMDBYTELcdlCalDeltaMM_p0_RxReplicaLcdlCalDeltaMM = this.HMDBYTELcdlCalDeltaMM_p0.RxReplicaLcdlCalDeltaMM;
		this.RxReplicaLcdlCalDeltaMM = this.HMDBYTELcdlCalDeltaMM_p0.RxReplicaLcdlCalDeltaMM;
      this.RxOffsetSelEvenSLn0_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn0_p0::type_id::create("RxOffsetSelEvenSLn0_p0",,get_full_name());
      if(this.RxOffsetSelEvenSLn0_p0.has_coverage(UVM_CVR_ALL))
      	this.RxOffsetSelEvenSLn0_p0.cg_bits.option.name = {get_name(), ".", "RxOffsetSelEvenSLn0_p0_bits"};
      this.RxOffsetSelEvenSLn0_p0.configure(this, null, "");
      this.RxOffsetSelEvenSLn0_p0.build();
      this.default_map.add_reg(this.RxOffsetSelEvenSLn0_p0, `UVM_REG_ADDR_WIDTH'h70, "RW", 0);
		this.RxOffsetSelEvenSLn0_p0_RxOffsetSelEvenSLn0_p0 = this.RxOffsetSelEvenSLn0_p0.RxOffsetSelEvenSLn0_p0;
      this.RxOffsetSelEvenSLn1_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn1_p0::type_id::create("RxOffsetSelEvenSLn1_p0",,get_full_name());
      if(this.RxOffsetSelEvenSLn1_p0.has_coverage(UVM_CVR_ALL))
      	this.RxOffsetSelEvenSLn1_p0.cg_bits.option.name = {get_name(), ".", "RxOffsetSelEvenSLn1_p0_bits"};
      this.RxOffsetSelEvenSLn1_p0.configure(this, null, "");
      this.RxOffsetSelEvenSLn1_p0.build();
      this.default_map.add_reg(this.RxOffsetSelEvenSLn1_p0, `UVM_REG_ADDR_WIDTH'h71, "RW", 0);
		this.RxOffsetSelEvenSLn1_p0_RxOffsetSelEvenSLn1_p0 = this.RxOffsetSelEvenSLn1_p0.RxOffsetSelEvenSLn1_p0;
      this.RxOffsetSelEvenSLn2_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn2_p0::type_id::create("RxOffsetSelEvenSLn2_p0",,get_full_name());
      if(this.RxOffsetSelEvenSLn2_p0.has_coverage(UVM_CVR_ALL))
      	this.RxOffsetSelEvenSLn2_p0.cg_bits.option.name = {get_name(), ".", "RxOffsetSelEvenSLn2_p0_bits"};
      this.RxOffsetSelEvenSLn2_p0.configure(this, null, "");
      this.RxOffsetSelEvenSLn2_p0.build();
      this.default_map.add_reg(this.RxOffsetSelEvenSLn2_p0, `UVM_REG_ADDR_WIDTH'h72, "RW", 0);
		this.RxOffsetSelEvenSLn2_p0_RxOffsetSelEvenSLn2_p0 = this.RxOffsetSelEvenSLn2_p0.RxOffsetSelEvenSLn2_p0;
      this.RxOffsetSelEvenSLn3_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelEvenSLn3_p0::type_id::create("RxOffsetSelEvenSLn3_p0",,get_full_name());
      if(this.RxOffsetSelEvenSLn3_p0.has_coverage(UVM_CVR_ALL))
      	this.RxOffsetSelEvenSLn3_p0.cg_bits.option.name = {get_name(), ".", "RxOffsetSelEvenSLn3_p0_bits"};
      this.RxOffsetSelEvenSLn3_p0.configure(this, null, "");
      this.RxOffsetSelEvenSLn3_p0.build();
      this.default_map.add_reg(this.RxOffsetSelEvenSLn3_p0, `UVM_REG_ADDR_WIDTH'h73, "RW", 0);
		this.RxOffsetSelEvenSLn3_p0_RxOffsetSelEvenSLn3_p0 = this.RxOffsetSelEvenSLn3_p0.RxOffsetSelEvenSLn3_p0;
      this.RxOffsetSelOddSLn0_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn0_p0::type_id::create("RxOffsetSelOddSLn0_p0",,get_full_name());
      if(this.RxOffsetSelOddSLn0_p0.has_coverage(UVM_CVR_ALL))
      	this.RxOffsetSelOddSLn0_p0.cg_bits.option.name = {get_name(), ".", "RxOffsetSelOddSLn0_p0_bits"};
      this.RxOffsetSelOddSLn0_p0.configure(this, null, "");
      this.RxOffsetSelOddSLn0_p0.build();
      this.default_map.add_reg(this.RxOffsetSelOddSLn0_p0, `UVM_REG_ADDR_WIDTH'h75, "RW", 0);
		this.RxOffsetSelOddSLn0_p0_RxOffsetSelOddSLn0_p0 = this.RxOffsetSelOddSLn0_p0.RxOffsetSelOddSLn0_p0;
      this.RxOffsetSelOddSLn1_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn1_p0::type_id::create("RxOffsetSelOddSLn1_p0",,get_full_name());
      if(this.RxOffsetSelOddSLn1_p0.has_coverage(UVM_CVR_ALL))
      	this.RxOffsetSelOddSLn1_p0.cg_bits.option.name = {get_name(), ".", "RxOffsetSelOddSLn1_p0_bits"};
      this.RxOffsetSelOddSLn1_p0.configure(this, null, "");
      this.RxOffsetSelOddSLn1_p0.build();
      this.default_map.add_reg(this.RxOffsetSelOddSLn1_p0, `UVM_REG_ADDR_WIDTH'h76, "RW", 0);
		this.RxOffsetSelOddSLn1_p0_RxOffsetSelOddSLn1_p0 = this.RxOffsetSelOddSLn1_p0.RxOffsetSelOddSLn1_p0;
      this.RxOffsetSelOddSLn2_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn2_p0::type_id::create("RxOffsetSelOddSLn2_p0",,get_full_name());
      if(this.RxOffsetSelOddSLn2_p0.has_coverage(UVM_CVR_ALL))
      	this.RxOffsetSelOddSLn2_p0.cg_bits.option.name = {get_name(), ".", "RxOffsetSelOddSLn2_p0_bits"};
      this.RxOffsetSelOddSLn2_p0.configure(this, null, "");
      this.RxOffsetSelOddSLn2_p0.build();
      this.default_map.add_reg(this.RxOffsetSelOddSLn2_p0, `UVM_REG_ADDR_WIDTH'h77, "RW", 0);
		this.RxOffsetSelOddSLn2_p0_RxOffsetSelOddSLn2_p0 = this.RxOffsetSelOddSLn2_p0.RxOffsetSelOddSLn2_p0;
      this.RxOffsetSelOddSLn3_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxOffsetSelOddSLn3_p0::type_id::create("RxOffsetSelOddSLn3_p0",,get_full_name());
      if(this.RxOffsetSelOddSLn3_p0.has_coverage(UVM_CVR_ALL))
      	this.RxOffsetSelOddSLn3_p0.cg_bits.option.name = {get_name(), ".", "RxOffsetSelOddSLn3_p0_bits"};
      this.RxOffsetSelOddSLn3_p0.configure(this, null, "");
      this.RxOffsetSelOddSLn3_p0.build();
      this.default_map.add_reg(this.RxOffsetSelOddSLn3_p0, `UVM_REG_ADDR_WIDTH'h78, "RW", 0);
		this.RxOffsetSelOddSLn3_p0_RxOffsetSelOddSLn3_p0 = this.RxOffsetSelOddSLn3_p0.RxOffsetSelOddSLn3_p0;
      this.RxModeX8Sel = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxModeX8Sel::type_id::create("RxModeX8Sel",,get_full_name());
      if(this.RxModeX8Sel.has_coverage(UVM_CVR_ALL))
      	this.RxModeX8Sel.cg_bits.option.name = {get_name(), ".", "RxModeX8Sel_bits"};
      this.RxModeX8Sel.configure(this, null, "");
      this.RxModeX8Sel.build();
      this.default_map.add_reg(this.RxModeX8Sel, `UVM_REG_ADDR_WIDTH'h7A, "RW", 0);
		this.RxModeX8Sel_RxModeX8Sel = this.RxModeX8Sel.RxModeX8Sel;
      this.ScratchPadHMDBYTE = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_ScratchPadHMDBYTE::type_id::create("ScratchPadHMDBYTE",,get_full_name());
      if(this.ScratchPadHMDBYTE.has_coverage(UVM_CVR_ALL))
      	this.ScratchPadHMDBYTE.cg_bits.option.name = {get_name(), ".", "ScratchPadHMDBYTE_bits"};
      this.ScratchPadHMDBYTE.configure(this, null, "");
      this.ScratchPadHMDBYTE.build();
      this.default_map.add_reg(this.ScratchPadHMDBYTE, `UVM_REG_ADDR_WIDTH'h7D, "RW", 0);
		this.ScratchPadHMDBYTE_ScratchPadHMDBYTE = this.ScratchPadHMDBYTE.ScratchPadHMDBYTE;
      this.LcdlTstPhase = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_LcdlTstPhase::type_id::create("LcdlTstPhase",,get_full_name());
      if(this.LcdlTstPhase.has_coverage(UVM_CVR_ALL))
      	this.LcdlTstPhase.cg_bits.option.name = {get_name(), ".", "LcdlTstPhase_bits"};
      this.LcdlTstPhase.configure(this, null, "");
      this.LcdlTstPhase.build();
      this.default_map.add_reg(this.LcdlTstPhase, `UVM_REG_ADDR_WIDTH'h84, "RW", 0);
		this.LcdlTstPhase_LcdlTstPhase = this.LcdlTstPhase.LcdlTstPhase;
      this.HMRxReplicaLcdlSeed_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMRxReplicaLcdlSeed_p0::type_id::create("HMRxReplicaLcdlSeed_p0",,get_full_name());
      if(this.HMRxReplicaLcdlSeed_p0.has_coverage(UVM_CVR_ALL))
      	this.HMRxReplicaLcdlSeed_p0.cg_bits.option.name = {get_name(), ".", "HMRxReplicaLcdlSeed_p0_bits"};
      this.HMRxReplicaLcdlSeed_p0.configure(this, null, "");
      this.HMRxReplicaLcdlSeed_p0.build();
      this.default_map.add_reg(this.HMRxReplicaLcdlSeed_p0, `UVM_REG_ADDR_WIDTH'h87, "RW", 0);
		this.HMRxReplicaLcdlSeed_p0_HMRxReplicaLcdlSeed_p0 = this.HMRxReplicaLcdlSeed_p0.HMRxReplicaLcdlSeed_p0;
      this.TxDiffDcaMode_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDiffDcaMode_p0::type_id::create("TxDiffDcaMode_p0",,get_full_name());
      if(this.TxDiffDcaMode_p0.has_coverage(UVM_CVR_ALL))
      	this.TxDiffDcaMode_p0.cg_bits.option.name = {get_name(), ".", "TxDiffDcaMode_p0_bits"};
      this.TxDiffDcaMode_p0.configure(this, null, "");
      this.TxDiffDcaMode_p0.build();
      this.default_map.add_reg(this.TxDiffDcaMode_p0, `UVM_REG_ADDR_WIDTH'h8D, "RW", 0);
		this.TxDiffDcaMode_p0_TxDiffDcaMode_p0 = this.TxDiffDcaMode_p0.TxDiffDcaMode_p0;
      this.DxCoreLoopBackMode = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DxCoreLoopBackMode::type_id::create("DxCoreLoopBackMode",,get_full_name());
      if(this.DxCoreLoopBackMode.has_coverage(UVM_CVR_ALL))
      	this.DxCoreLoopBackMode.cg_bits.option.name = {get_name(), ".", "DxCoreLoopBackMode_bits"};
      this.DxCoreLoopBackMode.configure(this, null, "");
      this.DxCoreLoopBackMode.build();
      this.default_map.add_reg(this.DxCoreLoopBackMode, `UVM_REG_ADDR_WIDTH'h91, "RW", 0);
		this.DxCoreLoopBackMode_DxCoreLoopBackMode = this.DxCoreLoopBackMode.DxCoreLoopBackMode;
      this.RxDFETap1SelTg0Ln0_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln0_p0::type_id::create("RxDFETap1SelTg0Ln0_p0",,get_full_name());
      if(this.RxDFETap1SelTg0Ln0_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap1SelTg0Ln0_p0.cg_bits.option.name = {get_name(), ".", "RxDFETap1SelTg0Ln0_p0_bits"};
      this.RxDFETap1SelTg0Ln0_p0.configure(this, null, "");
      this.RxDFETap1SelTg0Ln0_p0.build();
      this.default_map.add_reg(this.RxDFETap1SelTg0Ln0_p0, `UVM_REG_ADDR_WIDTH'hA0, "RW", 0);
		this.RxDFETap1SelTg0Ln0_p0_RxDFETap1SelTg0Ln0_p0 = this.RxDFETap1SelTg0Ln0_p0.RxDFETap1SelTg0Ln0_p0;
      this.RxDFETap1SelTg1Ln0_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln0_p0::type_id::create("RxDFETap1SelTg1Ln0_p0",,get_full_name());
      if(this.RxDFETap1SelTg1Ln0_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap1SelTg1Ln0_p0.cg_bits.option.name = {get_name(), ".", "RxDFETap1SelTg1Ln0_p0_bits"};
      this.RxDFETap1SelTg1Ln0_p0.configure(this, null, "");
      this.RxDFETap1SelTg1Ln0_p0.build();
      this.default_map.add_reg(this.RxDFETap1SelTg1Ln0_p0, `UVM_REG_ADDR_WIDTH'hA1, "RW", 0);
		this.RxDFETap1SelTg1Ln0_p0_RxDFETap1SelTg1Ln0_p0 = this.RxDFETap1SelTg1Ln0_p0.RxDFETap1SelTg1Ln0_p0;
      this.RxDFETap2SelTg0Ln0_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln0_p0::type_id::create("RxDFETap2SelTg0Ln0_p0",,get_full_name());
      if(this.RxDFETap2SelTg0Ln0_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap2SelTg0Ln0_p0.cg_bits.option.name = {get_name(), ".", "RxDFETap2SelTg0Ln0_p0_bits"};
      this.RxDFETap2SelTg0Ln0_p0.configure(this, null, "");
      this.RxDFETap2SelTg0Ln0_p0.build();
      this.default_map.add_reg(this.RxDFETap2SelTg0Ln0_p0, `UVM_REG_ADDR_WIDTH'hA4, "RW", 0);
		this.RxDFETap2SelTg0Ln0_p0_RxDFETap2SelTg0Ln0_p0 = this.RxDFETap2SelTg0Ln0_p0.RxDFETap2SelTg0Ln0_p0;
      this.RxDFETap2SelTg1Ln0_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln0_p0::type_id::create("RxDFETap2SelTg1Ln0_p0",,get_full_name());
      if(this.RxDFETap2SelTg1Ln0_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap2SelTg1Ln0_p0.cg_bits.option.name = {get_name(), ".", "RxDFETap2SelTg1Ln0_p0_bits"};
      this.RxDFETap2SelTg1Ln0_p0.configure(this, null, "");
      this.RxDFETap2SelTg1Ln0_p0.build();
      this.default_map.add_reg(this.RxDFETap2SelTg1Ln0_p0, `UVM_REG_ADDR_WIDTH'hA5, "RW", 0);
		this.RxDFETap2SelTg1Ln0_p0_RxDFETap2SelTg1Ln0_p0 = this.RxDFETap2SelTg1Ln0_p0.RxDFETap2SelTg1Ln0_p0;
      this.RxDFETap1SelTg0Ln1_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln1_p0::type_id::create("RxDFETap1SelTg0Ln1_p0",,get_full_name());
      if(this.RxDFETap1SelTg0Ln1_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap1SelTg0Ln1_p0.cg_bits.option.name = {get_name(), ".", "RxDFETap1SelTg0Ln1_p0_bits"};
      this.RxDFETap1SelTg0Ln1_p0.configure(this, null, "");
      this.RxDFETap1SelTg0Ln1_p0.build();
      this.default_map.add_reg(this.RxDFETap1SelTg0Ln1_p0, `UVM_REG_ADDR_WIDTH'hB0, "RW", 0);
		this.RxDFETap1SelTg0Ln1_p0_RxDFETap1SelTg0Ln1_p0 = this.RxDFETap1SelTg0Ln1_p0.RxDFETap1SelTg0Ln1_p0;
      this.RxDFETap1SelTg1Ln1_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln1_p0::type_id::create("RxDFETap1SelTg1Ln1_p0",,get_full_name());
      if(this.RxDFETap1SelTg1Ln1_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap1SelTg1Ln1_p0.cg_bits.option.name = {get_name(), ".", "RxDFETap1SelTg1Ln1_p0_bits"};
      this.RxDFETap1SelTg1Ln1_p0.configure(this, null, "");
      this.RxDFETap1SelTg1Ln1_p0.build();
      this.default_map.add_reg(this.RxDFETap1SelTg1Ln1_p0, `UVM_REG_ADDR_WIDTH'hB1, "RW", 0);
		this.RxDFETap1SelTg1Ln1_p0_RxDFETap1SelTg1Ln1_p0 = this.RxDFETap1SelTg1Ln1_p0.RxDFETap1SelTg1Ln1_p0;
      this.RxDFETap2SelTg0Ln1_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln1_p0::type_id::create("RxDFETap2SelTg0Ln1_p0",,get_full_name());
      if(this.RxDFETap2SelTg0Ln1_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap2SelTg0Ln1_p0.cg_bits.option.name = {get_name(), ".", "RxDFETap2SelTg0Ln1_p0_bits"};
      this.RxDFETap2SelTg0Ln1_p0.configure(this, null, "");
      this.RxDFETap2SelTg0Ln1_p0.build();
      this.default_map.add_reg(this.RxDFETap2SelTg0Ln1_p0, `UVM_REG_ADDR_WIDTH'hB4, "RW", 0);
		this.RxDFETap2SelTg0Ln1_p0_RxDFETap2SelTg0Ln1_p0 = this.RxDFETap2SelTg0Ln1_p0.RxDFETap2SelTg0Ln1_p0;
      this.RxDFETap2SelTg1Ln1_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln1_p0::type_id::create("RxDFETap2SelTg1Ln1_p0",,get_full_name());
      if(this.RxDFETap2SelTg1Ln1_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap2SelTg1Ln1_p0.cg_bits.option.name = {get_name(), ".", "RxDFETap2SelTg1Ln1_p0_bits"};
      this.RxDFETap2SelTg1Ln1_p0.configure(this, null, "");
      this.RxDFETap2SelTg1Ln1_p0.build();
      this.default_map.add_reg(this.RxDFETap2SelTg1Ln1_p0, `UVM_REG_ADDR_WIDTH'hB5, "RW", 0);
		this.RxDFETap2SelTg1Ln1_p0_RxDFETap2SelTg1Ln1_p0 = this.RxDFETap2SelTg1Ln1_p0.RxDFETap2SelTg1Ln1_p0;
      this.RxDFETap1SelTg0Ln2_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln2_p0::type_id::create("RxDFETap1SelTg0Ln2_p0",,get_full_name());
      if(this.RxDFETap1SelTg0Ln2_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap1SelTg0Ln2_p0.cg_bits.option.name = {get_name(), ".", "RxDFETap1SelTg0Ln2_p0_bits"};
      this.RxDFETap1SelTg0Ln2_p0.configure(this, null, "");
      this.RxDFETap1SelTg0Ln2_p0.build();
      this.default_map.add_reg(this.RxDFETap1SelTg0Ln2_p0, `UVM_REG_ADDR_WIDTH'hC0, "RW", 0);
		this.RxDFETap1SelTg0Ln2_p0_RxDFETap1SelTg0Ln2_p0 = this.RxDFETap1SelTg0Ln2_p0.RxDFETap1SelTg0Ln2_p0;
      this.RxDFETap1SelTg1Ln2_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln2_p0::type_id::create("RxDFETap1SelTg1Ln2_p0",,get_full_name());
      if(this.RxDFETap1SelTg1Ln2_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap1SelTg1Ln2_p0.cg_bits.option.name = {get_name(), ".", "RxDFETap1SelTg1Ln2_p0_bits"};
      this.RxDFETap1SelTg1Ln2_p0.configure(this, null, "");
      this.RxDFETap1SelTg1Ln2_p0.build();
      this.default_map.add_reg(this.RxDFETap1SelTg1Ln2_p0, `UVM_REG_ADDR_WIDTH'hC1, "RW", 0);
		this.RxDFETap1SelTg1Ln2_p0_RxDFETap1SelTg1Ln2_p0 = this.RxDFETap1SelTg1Ln2_p0.RxDFETap1SelTg1Ln2_p0;
      this.RxDFETap2SelTg0Ln2_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln2_p0::type_id::create("RxDFETap2SelTg0Ln2_p0",,get_full_name());
      if(this.RxDFETap2SelTg0Ln2_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap2SelTg0Ln2_p0.cg_bits.option.name = {get_name(), ".", "RxDFETap2SelTg0Ln2_p0_bits"};
      this.RxDFETap2SelTg0Ln2_p0.configure(this, null, "");
      this.RxDFETap2SelTg0Ln2_p0.build();
      this.default_map.add_reg(this.RxDFETap2SelTg0Ln2_p0, `UVM_REG_ADDR_WIDTH'hC4, "RW", 0);
		this.RxDFETap2SelTg0Ln2_p0_RxDFETap2SelTg0Ln2_p0 = this.RxDFETap2SelTg0Ln2_p0.RxDFETap2SelTg0Ln2_p0;
      this.RxDFETap2SelTg1Ln2_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln2_p0::type_id::create("RxDFETap2SelTg1Ln2_p0",,get_full_name());
      if(this.RxDFETap2SelTg1Ln2_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap2SelTg1Ln2_p0.cg_bits.option.name = {get_name(), ".", "RxDFETap2SelTg1Ln2_p0_bits"};
      this.RxDFETap2SelTg1Ln2_p0.configure(this, null, "");
      this.RxDFETap2SelTg1Ln2_p0.build();
      this.default_map.add_reg(this.RxDFETap2SelTg1Ln2_p0, `UVM_REG_ADDR_WIDTH'hC5, "RW", 0);
		this.RxDFETap2SelTg1Ln2_p0_RxDFETap2SelTg1Ln2_p0 = this.RxDFETap2SelTg1Ln2_p0.RxDFETap2SelTg1Ln2_p0;
      this.RxDFETap1SelTg0Ln3_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg0Ln3_p0::type_id::create("RxDFETap1SelTg0Ln3_p0",,get_full_name());
      if(this.RxDFETap1SelTg0Ln3_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap1SelTg0Ln3_p0.cg_bits.option.name = {get_name(), ".", "RxDFETap1SelTg0Ln3_p0_bits"};
      this.RxDFETap1SelTg0Ln3_p0.configure(this, null, "");
      this.RxDFETap1SelTg0Ln3_p0.build();
      this.default_map.add_reg(this.RxDFETap1SelTg0Ln3_p0, `UVM_REG_ADDR_WIDTH'hD0, "RW", 0);
		this.RxDFETap1SelTg0Ln3_p0_RxDFETap1SelTg0Ln3_p0 = this.RxDFETap1SelTg0Ln3_p0.RxDFETap1SelTg0Ln3_p0;
      this.RxDFETap1SelTg1Ln3_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap1SelTg1Ln3_p0::type_id::create("RxDFETap1SelTg1Ln3_p0",,get_full_name());
      if(this.RxDFETap1SelTg1Ln3_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap1SelTg1Ln3_p0.cg_bits.option.name = {get_name(), ".", "RxDFETap1SelTg1Ln3_p0_bits"};
      this.RxDFETap1SelTg1Ln3_p0.configure(this, null, "");
      this.RxDFETap1SelTg1Ln3_p0.build();
      this.default_map.add_reg(this.RxDFETap1SelTg1Ln3_p0, `UVM_REG_ADDR_WIDTH'hD1, "RW", 0);
		this.RxDFETap1SelTg1Ln3_p0_RxDFETap1SelTg1Ln3_p0 = this.RxDFETap1SelTg1Ln3_p0.RxDFETap1SelTg1Ln3_p0;
      this.RxDFETap2SelTg0Ln3_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg0Ln3_p0::type_id::create("RxDFETap2SelTg0Ln3_p0",,get_full_name());
      if(this.RxDFETap2SelTg0Ln3_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap2SelTg0Ln3_p0.cg_bits.option.name = {get_name(), ".", "RxDFETap2SelTg0Ln3_p0_bits"};
      this.RxDFETap2SelTg0Ln3_p0.configure(this, null, "");
      this.RxDFETap2SelTg0Ln3_p0.build();
      this.default_map.add_reg(this.RxDFETap2SelTg0Ln3_p0, `UVM_REG_ADDR_WIDTH'hD4, "RW", 0);
		this.RxDFETap2SelTg0Ln3_p0_RxDFETap2SelTg0Ln3_p0 = this.RxDFETap2SelTg0Ln3_p0.RxDFETap2SelTg0Ln3_p0;
      this.RxDFETap2SelTg1Ln3_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDFETap2SelTg1Ln3_p0::type_id::create("RxDFETap2SelTg1Ln3_p0",,get_full_name());
      if(this.RxDFETap2SelTg1Ln3_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap2SelTg1Ln3_p0.cg_bits.option.name = {get_name(), ".", "RxDFETap2SelTg1Ln3_p0_bits"};
      this.RxDFETap2SelTg1Ln3_p0.configure(this, null, "");
      this.RxDFETap2SelTg1Ln3_p0.build();
      this.default_map.add_reg(this.RxDFETap2SelTg1Ln3_p0, `UVM_REG_ADDR_WIDTH'hD5, "RW", 0);
		this.RxDFETap2SelTg1Ln3_p0_RxDFETap2SelTg1Ln3_p0 = this.RxDFETap2SelTg1Ln3_p0.RxDFETap2SelTg1Ln3_p0;
      this.PclkDCACodeDqLn0_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn0_p0::type_id::create("PclkDCACodeDqLn0_p0",,get_full_name());
      if(this.PclkDCACodeDqLn0_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACodeDqLn0_p0.cg_bits.option.name = {get_name(), ".", "PclkDCACodeDqLn0_p0_bits"};
      this.PclkDCACodeDqLn0_p0.configure(this, null, "");
      this.PclkDCACodeDqLn0_p0.build();
      this.default_map.add_reg(this.PclkDCACodeDqLn0_p0, `UVM_REG_ADDR_WIDTH'hF0, "RW", 0);
		this.PclkDCACodeDqLn0_p0_PclkDCACoarseDqLn0 = this.PclkDCACodeDqLn0_p0.PclkDCACoarseDqLn0;
		this.PclkDCACoarseDqLn0 = this.PclkDCACodeDqLn0_p0.PclkDCACoarseDqLn0;
		this.PclkDCACodeDqLn0_p0_PclkDCAFineDqLn0 = this.PclkDCACodeDqLn0_p0.PclkDCAFineDqLn0;
		this.PclkDCAFineDqLn0 = this.PclkDCACodeDqLn0_p0.PclkDCAFineDqLn0;
      this.PclkDCACodeDqLn1_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn1_p0::type_id::create("PclkDCACodeDqLn1_p0",,get_full_name());
      if(this.PclkDCACodeDqLn1_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACodeDqLn1_p0.cg_bits.option.name = {get_name(), ".", "PclkDCACodeDqLn1_p0_bits"};
      this.PclkDCACodeDqLn1_p0.configure(this, null, "");
      this.PclkDCACodeDqLn1_p0.build();
      this.default_map.add_reg(this.PclkDCACodeDqLn1_p0, `UVM_REG_ADDR_WIDTH'hF1, "RW", 0);
		this.PclkDCACodeDqLn1_p0_PclkDCACoarseDqLn1 = this.PclkDCACodeDqLn1_p0.PclkDCACoarseDqLn1;
		this.PclkDCACoarseDqLn1 = this.PclkDCACodeDqLn1_p0.PclkDCACoarseDqLn1;
		this.PclkDCACodeDqLn1_p0_PclkDCAFineDqLn1 = this.PclkDCACodeDqLn1_p0.PclkDCAFineDqLn1;
		this.PclkDCAFineDqLn1 = this.PclkDCACodeDqLn1_p0.PclkDCAFineDqLn1;
      this.PclkDCACodeDqLn2_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn2_p0::type_id::create("PclkDCACodeDqLn2_p0",,get_full_name());
      if(this.PclkDCACodeDqLn2_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACodeDqLn2_p0.cg_bits.option.name = {get_name(), ".", "PclkDCACodeDqLn2_p0_bits"};
      this.PclkDCACodeDqLn2_p0.configure(this, null, "");
      this.PclkDCACodeDqLn2_p0.build();
      this.default_map.add_reg(this.PclkDCACodeDqLn2_p0, `UVM_REG_ADDR_WIDTH'hF2, "RW", 0);
		this.PclkDCACodeDqLn2_p0_PclkDCACoarseDqLn2 = this.PclkDCACodeDqLn2_p0.PclkDCACoarseDqLn2;
		this.PclkDCACoarseDqLn2 = this.PclkDCACodeDqLn2_p0.PclkDCACoarseDqLn2;
		this.PclkDCACodeDqLn2_p0_PclkDCAFineDqLn2 = this.PclkDCACodeDqLn2_p0.PclkDCAFineDqLn2;
		this.PclkDCAFineDqLn2 = this.PclkDCACodeDqLn2_p0.PclkDCAFineDqLn2;
      this.PclkDCACodeDqLn3_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDqLn3_p0::type_id::create("PclkDCACodeDqLn3_p0",,get_full_name());
      if(this.PclkDCACodeDqLn3_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACodeDqLn3_p0.cg_bits.option.name = {get_name(), ".", "PclkDCACodeDqLn3_p0_bits"};
      this.PclkDCACodeDqLn3_p0.configure(this, null, "");
      this.PclkDCACodeDqLn3_p0.build();
      this.default_map.add_reg(this.PclkDCACodeDqLn3_p0, `UVM_REG_ADDR_WIDTH'hF3, "RW", 0);
		this.PclkDCACodeDqLn3_p0_PclkDCACoarseDqLn3 = this.PclkDCACodeDqLn3_p0.PclkDCACoarseDqLn3;
		this.PclkDCACoarseDqLn3 = this.PclkDCACodeDqLn3_p0.PclkDCACoarseDqLn3;
		this.PclkDCACodeDqLn3_p0_PclkDCAFineDqLn3 = this.PclkDCACodeDqLn3_p0.PclkDCAFineDqLn3;
		this.PclkDCAFineDqLn3 = this.PclkDCACodeDqLn3_p0.PclkDCAFineDqLn3;
      this.PclkDCACodeDQS_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACodeDQS_p0::type_id::create("PclkDCACodeDQS_p0",,get_full_name());
      if(this.PclkDCACodeDQS_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACodeDQS_p0.cg_bits.option.name = {get_name(), ".", "PclkDCACodeDQS_p0_bits"};
      this.PclkDCACodeDQS_p0.configure(this, null, "");
      this.PclkDCACodeDQS_p0.build();
      this.default_map.add_reg(this.PclkDCACodeDQS_p0, `UVM_REG_ADDR_WIDTH'hF5, "RW", 0);
		this.PclkDCACodeDQS_p0_PclkDCACoarseDQS = this.PclkDCACodeDQS_p0.PclkDCACoarseDQS;
		this.PclkDCACoarseDQS = this.PclkDCACodeDQS_p0.PclkDCACoarseDQS;
		this.PclkDCACodeDQS_p0_PclkDCAFineDQS = this.PclkDCACodeDQS_p0.PclkDCAFineDQS;
		this.PclkDCAFineDQS = this.PclkDCACodeDQS_p0.PclkDCAFineDQS;
      this.HardMacroModeSel = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HardMacroModeSel::type_id::create("HardMacroModeSel",,get_full_name());
      if(this.HardMacroModeSel.has_coverage(UVM_CVR_ALL))
      	this.HardMacroModeSel.cg_bits.option.name = {get_name(), ".", "HardMacroModeSel_bits"};
      this.HardMacroModeSel.configure(this, null, "");
      this.HardMacroModeSel.build();
      this.default_map.add_reg(this.HardMacroModeSel, `UVM_REG_ADDR_WIDTH'hF6, "RW", 0);
		this.HardMacroModeSel_HardMacroModeSel = this.HardMacroModeSel.HardMacroModeSel;
      this.TxFuncMode = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxFuncMode::type_id::create("TxFuncMode",,get_full_name());
      if(this.TxFuncMode.has_coverage(UVM_CVR_ALL))
      	this.TxFuncMode.cg_bits.option.name = {get_name(), ".", "TxFuncMode_bits"};
      this.TxFuncMode.configure(this, null, "");
      this.TxFuncMode.build();
      this.default_map.add_reg(this.TxFuncMode, `UVM_REG_ADDR_WIDTH'hF8, "RW", 0);
		this.TxFuncMode_TxFuncMode = this.TxFuncMode.TxFuncMode;
      this.HMReserved0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMReserved0::type_id::create("HMReserved0",,get_full_name());
      if(this.HMReserved0.has_coverage(UVM_CVR_ALL))
      	this.HMReserved0.cg_bits.option.name = {get_name(), ".", "HMReserved0_bits"};
      this.HMReserved0.configure(this, null, "");
      this.HMReserved0.build();
      this.default_map.add_reg(this.HMReserved0, `UVM_REG_ADDR_WIDTH'hFE, "RW", 0);
		this.HMReserved0_HMReserved0 = this.HMReserved0.HMReserved0;
      this.HMReservedP1_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_HMReservedP1_p0::type_id::create("HMReservedP1_p0",,get_full_name());
      if(this.HMReservedP1_p0.has_coverage(UVM_CVR_ALL))
      	this.HMReservedP1_p0.cg_bits.option.name = {get_name(), ".", "HMReservedP1_p0_bits"};
      this.HMReservedP1_p0.configure(this, null, "");
      this.HMReservedP1_p0.build();
      this.default_map.add_reg(this.HMReservedP1_p0, `UVM_REG_ADDR_WIDTH'hFF, "RW", 0);
		this.HMReservedP1_p0_HMReservedP1_p0 = this.HMReservedP1_p0.HMReservedP1_p0;
      this.PclkDCATxLcdlPhase_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCATxLcdlPhase_p0::type_id::create("PclkDCATxLcdlPhase_p0",,get_full_name());
      if(this.PclkDCATxLcdlPhase_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCATxLcdlPhase_p0.cg_bits.option.name = {get_name(), ".", "PclkDCATxLcdlPhase_p0_bits"};
      this.PclkDCATxLcdlPhase_p0.configure(this, null, "");
      this.PclkDCATxLcdlPhase_p0.build();
      this.default_map.add_reg(this.PclkDCATxLcdlPhase_p0, `UVM_REG_ADDR_WIDTH'h110, "RW", 0);
		this.PclkDCATxLcdlPhase_p0_PclkDCATxLcdlPhase_p0 = this.PclkDCATxLcdlPhase_p0.PclkDCATxLcdlPhase_p0;
      this.RxReplicaLcdlDbgCntl2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxReplicaLcdlDbgCntl2::type_id::create("RxReplicaLcdlDbgCntl2",,get_full_name());
      if(this.RxReplicaLcdlDbgCntl2.has_coverage(UVM_CVR_ALL))
      	this.RxReplicaLcdlDbgCntl2.cg_bits.option.name = {get_name(), ".", "RxReplicaLcdlDbgCntl2_bits"};
      this.RxReplicaLcdlDbgCntl2.configure(this, null, "");
      this.RxReplicaLcdlDbgCntl2.build();
      this.default_map.add_reg(this.RxReplicaLcdlDbgCntl2, `UVM_REG_ADDR_WIDTH'h185, "RW", 0);
		this.RxReplicaLcdlDbgCntl2_RxReplicaLcdlStickyUnlockThreshold = this.RxReplicaLcdlDbgCntl2.RxReplicaLcdlStickyUnlockThreshold;
		this.RxReplicaLcdlStickyUnlockThreshold = this.RxReplicaLcdlDbgCntl2.RxReplicaLcdlStickyUnlockThreshold;
      this.RxReplicaLcdlCalPhase = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxReplicaLcdlCalPhase::type_id::create("RxReplicaLcdlCalPhase",,get_full_name());
      if(this.RxReplicaLcdlCalPhase.has_coverage(UVM_CVR_ALL))
      	this.RxReplicaLcdlCalPhase.cg_bits.option.name = {get_name(), ".", "RxReplicaLcdlCalPhase_bits"};
      this.RxReplicaLcdlCalPhase.configure(this, null, "");
      this.RxReplicaLcdlCalPhase.build();
      this.default_map.add_reg(this.RxReplicaLcdlCalPhase, `UVM_REG_ADDR_WIDTH'h188, "RW", 0);
		this.RxReplicaLcdlCalPhase_RxReplicaLcdlCalPhase = this.RxReplicaLcdlCalPhase.RxReplicaLcdlCalPhase;
      this.PclkDCDOffsetDqLn0_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn0_p0::type_id::create("PclkDCDOffsetDqLn0_p0",,get_full_name());
      if(this.PclkDCDOffsetDqLn0_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCDOffsetDqLn0_p0.cg_bits.option.name = {get_name(), ".", "PclkDCDOffsetDqLn0_p0_bits"};
      this.PclkDCDOffsetDqLn0_p0.configure(this, null, "");
      this.PclkDCDOffsetDqLn0_p0.build();
      this.default_map.add_reg(this.PclkDCDOffsetDqLn0_p0, `UVM_REG_ADDR_WIDTH'h200, "RW", 0);
		this.PclkDCDOffsetDqLn0_p0_PclkDCDOffsetDqLn0_p0 = this.PclkDCDOffsetDqLn0_p0.PclkDCDOffsetDqLn0_p0;
      this.PclkDCDOffsetDqLn1_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn1_p0::type_id::create("PclkDCDOffsetDqLn1_p0",,get_full_name());
      if(this.PclkDCDOffsetDqLn1_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCDOffsetDqLn1_p0.cg_bits.option.name = {get_name(), ".", "PclkDCDOffsetDqLn1_p0_bits"};
      this.PclkDCDOffsetDqLn1_p0.configure(this, null, "");
      this.PclkDCDOffsetDqLn1_p0.build();
      this.default_map.add_reg(this.PclkDCDOffsetDqLn1_p0, `UVM_REG_ADDR_WIDTH'h201, "RW", 0);
		this.PclkDCDOffsetDqLn1_p0_PclkDCDOffsetDqLn1_p0 = this.PclkDCDOffsetDqLn1_p0.PclkDCDOffsetDqLn1_p0;
      this.PclkDCDOffsetDqLn2_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn2_p0::type_id::create("PclkDCDOffsetDqLn2_p0",,get_full_name());
      if(this.PclkDCDOffsetDqLn2_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCDOffsetDqLn2_p0.cg_bits.option.name = {get_name(), ".", "PclkDCDOffsetDqLn2_p0_bits"};
      this.PclkDCDOffsetDqLn2_p0.configure(this, null, "");
      this.PclkDCDOffsetDqLn2_p0.build();
      this.default_map.add_reg(this.PclkDCDOffsetDqLn2_p0, `UVM_REG_ADDR_WIDTH'h202, "RW", 0);
		this.PclkDCDOffsetDqLn2_p0_PclkDCDOffsetDqLn2_p0 = this.PclkDCDOffsetDqLn2_p0.PclkDCDOffsetDqLn2_p0;
      this.PclkDCDOffsetDqLn3_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDqLn3_p0::type_id::create("PclkDCDOffsetDqLn3_p0",,get_full_name());
      if(this.PclkDCDOffsetDqLn3_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCDOffsetDqLn3_p0.cg_bits.option.name = {get_name(), ".", "PclkDCDOffsetDqLn3_p0_bits"};
      this.PclkDCDOffsetDqLn3_p0.configure(this, null, "");
      this.PclkDCDOffsetDqLn3_p0.build();
      this.default_map.add_reg(this.PclkDCDOffsetDqLn3_p0, `UVM_REG_ADDR_WIDTH'h203, "RW", 0);
		this.PclkDCDOffsetDqLn3_p0_PclkDCDOffsetDqLn3_p0 = this.PclkDCDOffsetDqLn3_p0.PclkDCDOffsetDqLn3_p0;
      this.PclkDCDOffsetDQS_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCDOffsetDQS_p0::type_id::create("PclkDCDOffsetDQS_p0",,get_full_name());
      if(this.PclkDCDOffsetDQS_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCDOffsetDQS_p0.cg_bits.option.name = {get_name(), ".", "PclkDCDOffsetDQS_p0_bits"};
      this.PclkDCDOffsetDQS_p0.configure(this, null, "");
      this.PclkDCDOffsetDQS_p0.build();
      this.default_map.add_reg(this.PclkDCDOffsetDQS_p0, `UVM_REG_ADDR_WIDTH'h205, "RW", 0);
		this.PclkDCDOffsetDQS_p0_PclkDCDOffsetDQS_p0 = this.PclkDCDOffsetDQS_p0.PclkDCDOffsetDQS_p0;
      this.PclkDCACalSampDqLn0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn0::type_id::create("PclkDCACalSampDqLn0",,get_full_name());
      if(this.PclkDCACalSampDqLn0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACalSampDqLn0.cg_bits.option.name = {get_name(), ".", "PclkDCACalSampDqLn0_bits"};
      this.PclkDCACalSampDqLn0.configure(this, null, "");
      this.PclkDCACalSampDqLn0.build();
      this.default_map.add_reg(this.PclkDCACalSampDqLn0, `UVM_REG_ADDR_WIDTH'h300, "RO", 0);
		this.PclkDCACalSampDqLn0_PclkDCACalSampDqLn0 = this.PclkDCACalSampDqLn0.PclkDCACalSampDqLn0;
      this.PclkDCACalSampDqLn1 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn1::type_id::create("PclkDCACalSampDqLn1",,get_full_name());
      if(this.PclkDCACalSampDqLn1.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACalSampDqLn1.cg_bits.option.name = {get_name(), ".", "PclkDCACalSampDqLn1_bits"};
      this.PclkDCACalSampDqLn1.configure(this, null, "");
      this.PclkDCACalSampDqLn1.build();
      this.default_map.add_reg(this.PclkDCACalSampDqLn1, `UVM_REG_ADDR_WIDTH'h301, "RO", 0);
		this.PclkDCACalSampDqLn1_PclkDCACalSampDqLn1 = this.PclkDCACalSampDqLn1.PclkDCACalSampDqLn1;
      this.PclkDCACalSampDqLn2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn2::type_id::create("PclkDCACalSampDqLn2",,get_full_name());
      if(this.PclkDCACalSampDqLn2.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACalSampDqLn2.cg_bits.option.name = {get_name(), ".", "PclkDCACalSampDqLn2_bits"};
      this.PclkDCACalSampDqLn2.configure(this, null, "");
      this.PclkDCACalSampDqLn2.build();
      this.default_map.add_reg(this.PclkDCACalSampDqLn2, `UVM_REG_ADDR_WIDTH'h302, "RO", 0);
		this.PclkDCACalSampDqLn2_PclkDCACalSampDqLn2 = this.PclkDCACalSampDqLn2.PclkDCACalSampDqLn2;
      this.PclkDCACalSampDqLn3 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDqLn3::type_id::create("PclkDCACalSampDqLn3",,get_full_name());
      if(this.PclkDCACalSampDqLn3.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACalSampDqLn3.cg_bits.option.name = {get_name(), ".", "PclkDCACalSampDqLn3_bits"};
      this.PclkDCACalSampDqLn3.configure(this, null, "");
      this.PclkDCACalSampDqLn3.build();
      this.default_map.add_reg(this.PclkDCACalSampDqLn3, `UVM_REG_ADDR_WIDTH'h303, "RO", 0);
		this.PclkDCACalSampDqLn3_PclkDCACalSampDqLn3 = this.PclkDCACalSampDqLn3.PclkDCACalSampDqLn3;
      this.PclkDCACalSampDQS = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCACalSampDQS::type_id::create("PclkDCACalSampDQS",,get_full_name());
      if(this.PclkDCACalSampDQS.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACalSampDQS.cg_bits.option.name = {get_name(), ".", "PclkDCACalSampDQS_bits"};
      this.PclkDCACalSampDQS.configure(this, null, "");
      this.PclkDCACalSampDQS.build();
      this.default_map.add_reg(this.PclkDCACalSampDQS, `UVM_REG_ADDR_WIDTH'h305, "RO", 0);
		this.PclkDCACalSampDQS_PclkDCACalSampDQS = this.PclkDCACalSampDQS.PclkDCACalSampDQS;
      this.PclkDCAResults = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCAResults::type_id::create("PclkDCAResults",,get_full_name());
      if(this.PclkDCAResults.has_coverage(UVM_CVR_ALL))
      	this.PclkDCAResults.cg_bits.option.name = {get_name(), ".", "PclkDCAResults_bits"};
      this.PclkDCAResults.configure(this, null, "");
      this.PclkDCAResults.build();
      this.default_map.add_reg(this.PclkDCAResults, `UVM_REG_ADDR_WIDTH'h30A, "RO", 0);
		this.PclkDCAResults_PclkDCADone = this.PclkDCAResults.PclkDCADone;
		this.PclkDCADone = this.PclkDCAResults.PclkDCADone;
		this.PclkDCAResults_PclkDCASuccessful = this.PclkDCAResults.PclkDCASuccessful;
		this.PclkDCASuccessful = this.PclkDCAResults.PclkDCASuccessful;
      this.RxFifoWrInfoLn0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn0::type_id::create("RxFifoWrInfoLn0",,get_full_name());
      if(this.RxFifoWrInfoLn0.has_coverage(UVM_CVR_ALL))
      	this.RxFifoWrInfoLn0.cg_bits.option.name = {get_name(), ".", "RxFifoWrInfoLn0_bits"};
      this.RxFifoWrInfoLn0.configure(this, null, "");
      this.RxFifoWrInfoLn0.build();
      this.default_map.add_reg(this.RxFifoWrInfoLn0, `UVM_REG_ADDR_WIDTH'h320, "RO", 0);
		this.RxFifoWrInfoLn0_RxFifoWrLocEvnLn0 = this.RxFifoWrInfoLn0.RxFifoWrLocEvnLn0;
		this.RxFifoWrLocEvnLn0 = this.RxFifoWrInfoLn0.RxFifoWrLocEvnLn0;
		this.RxFifoWrInfoLn0_RxFifoWrLocOddLn0 = this.RxFifoWrInfoLn0.RxFifoWrLocOddLn0;
		this.RxFifoWrLocOddLn0 = this.RxFifoWrInfoLn0.RxFifoWrLocOddLn0;
      this.RxFifoWrInfoLn1 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn1::type_id::create("RxFifoWrInfoLn1",,get_full_name());
      if(this.RxFifoWrInfoLn1.has_coverage(UVM_CVR_ALL))
      	this.RxFifoWrInfoLn1.cg_bits.option.name = {get_name(), ".", "RxFifoWrInfoLn1_bits"};
      this.RxFifoWrInfoLn1.configure(this, null, "");
      this.RxFifoWrInfoLn1.build();
      this.default_map.add_reg(this.RxFifoWrInfoLn1, `UVM_REG_ADDR_WIDTH'h321, "RO", 0);
		this.RxFifoWrInfoLn1_RxFifoWrLocEvnLn1 = this.RxFifoWrInfoLn1.RxFifoWrLocEvnLn1;
		this.RxFifoWrLocEvnLn1 = this.RxFifoWrInfoLn1.RxFifoWrLocEvnLn1;
		this.RxFifoWrInfoLn1_RxFifoWrLocOddLn1 = this.RxFifoWrInfoLn1.RxFifoWrLocOddLn1;
		this.RxFifoWrLocOddLn1 = this.RxFifoWrInfoLn1.RxFifoWrLocOddLn1;
      this.RxFifoWrInfoLn2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn2::type_id::create("RxFifoWrInfoLn2",,get_full_name());
      if(this.RxFifoWrInfoLn2.has_coverage(UVM_CVR_ALL))
      	this.RxFifoWrInfoLn2.cg_bits.option.name = {get_name(), ".", "RxFifoWrInfoLn2_bits"};
      this.RxFifoWrInfoLn2.configure(this, null, "");
      this.RxFifoWrInfoLn2.build();
      this.default_map.add_reg(this.RxFifoWrInfoLn2, `UVM_REG_ADDR_WIDTH'h322, "RO", 0);
		this.RxFifoWrInfoLn2_RxFifoWrLocEvnLn2 = this.RxFifoWrInfoLn2.RxFifoWrLocEvnLn2;
		this.RxFifoWrLocEvnLn2 = this.RxFifoWrInfoLn2.RxFifoWrLocEvnLn2;
		this.RxFifoWrInfoLn2_RxFifoWrLocOddLn2 = this.RxFifoWrInfoLn2.RxFifoWrLocOddLn2;
		this.RxFifoWrLocOddLn2 = this.RxFifoWrInfoLn2.RxFifoWrLocOddLn2;
      this.RxFifoWrInfoLn3 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoWrInfoLn3::type_id::create("RxFifoWrInfoLn3",,get_full_name());
      if(this.RxFifoWrInfoLn3.has_coverage(UVM_CVR_ALL))
      	this.RxFifoWrInfoLn3.cg_bits.option.name = {get_name(), ".", "RxFifoWrInfoLn3_bits"};
      this.RxFifoWrInfoLn3.configure(this, null, "");
      this.RxFifoWrInfoLn3.build();
      this.default_map.add_reg(this.RxFifoWrInfoLn3, `UVM_REG_ADDR_WIDTH'h323, "RO", 0);
		this.RxFifoWrInfoLn3_RxFifoWrLocEvnLn3 = this.RxFifoWrInfoLn3.RxFifoWrLocEvnLn3;
		this.RxFifoWrLocEvnLn3 = this.RxFifoWrInfoLn3.RxFifoWrLocEvnLn3;
		this.RxFifoWrInfoLn3_RxFifoWrLocOddLn3 = this.RxFifoWrInfoLn3.RxFifoWrLocOddLn3;
		this.RxFifoWrLocOddLn3 = this.RxFifoWrInfoLn3.RxFifoWrLocOddLn3;
      this.RxFifoRdInfoLn0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn0::type_id::create("RxFifoRdInfoLn0",,get_full_name());
      if(this.RxFifoRdInfoLn0.has_coverage(UVM_CVR_ALL))
      	this.RxFifoRdInfoLn0.cg_bits.option.name = {get_name(), ".", "RxFifoRdInfoLn0_bits"};
      this.RxFifoRdInfoLn0.configure(this, null, "");
      this.RxFifoRdInfoLn0.build();
      this.default_map.add_reg(this.RxFifoRdInfoLn0, `UVM_REG_ADDR_WIDTH'h328, "RO", 0);
		this.RxFifoRdInfoLn0_RxFifoRdLocLn0 = this.RxFifoRdInfoLn0.RxFifoRdLocLn0;
		this.RxFifoRdLocLn0 = this.RxFifoRdInfoLn0.RxFifoRdLocLn0;
      this.RxFifoRdInfoLn1 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn1::type_id::create("RxFifoRdInfoLn1",,get_full_name());
      if(this.RxFifoRdInfoLn1.has_coverage(UVM_CVR_ALL))
      	this.RxFifoRdInfoLn1.cg_bits.option.name = {get_name(), ".", "RxFifoRdInfoLn1_bits"};
      this.RxFifoRdInfoLn1.configure(this, null, "");
      this.RxFifoRdInfoLn1.build();
      this.default_map.add_reg(this.RxFifoRdInfoLn1, `UVM_REG_ADDR_WIDTH'h329, "RO", 0);
		this.RxFifoRdInfoLn1_RxFifoRdLocLn1 = this.RxFifoRdInfoLn1.RxFifoRdLocLn1;
		this.RxFifoRdLocLn1 = this.RxFifoRdInfoLn1.RxFifoRdLocLn1;
      this.RxFifoRdInfoLn2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn2::type_id::create("RxFifoRdInfoLn2",,get_full_name());
      if(this.RxFifoRdInfoLn2.has_coverage(UVM_CVR_ALL))
      	this.RxFifoRdInfoLn2.cg_bits.option.name = {get_name(), ".", "RxFifoRdInfoLn2_bits"};
      this.RxFifoRdInfoLn2.configure(this, null, "");
      this.RxFifoRdInfoLn2.build();
      this.default_map.add_reg(this.RxFifoRdInfoLn2, `UVM_REG_ADDR_WIDTH'h32A, "RO", 0);
		this.RxFifoRdInfoLn2_RxFifoRdLocLn2 = this.RxFifoRdInfoLn2.RxFifoRdLocLn2;
		this.RxFifoRdLocLn2 = this.RxFifoRdInfoLn2.RxFifoRdLocLn2;
      this.RxFifoRdInfoLn3 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxFifoRdInfoLn3::type_id::create("RxFifoRdInfoLn3",,get_full_name());
      if(this.RxFifoRdInfoLn3.has_coverage(UVM_CVR_ALL))
      	this.RxFifoRdInfoLn3.cg_bits.option.name = {get_name(), ".", "RxFifoRdInfoLn3_bits"};
      this.RxFifoRdInfoLn3.configure(this, null, "");
      this.RxFifoRdInfoLn3.build();
      this.default_map.add_reg(this.RxFifoRdInfoLn3, `UVM_REG_ADDR_WIDTH'h32B, "RO", 0);
		this.RxFifoRdInfoLn3_RxFifoRdLocLn3 = this.RxFifoRdInfoLn3.RxFifoRdLocLn3;
		this.RxFifoRdLocLn3 = this.RxFifoRdInfoLn3.RxFifoRdLocLn3;
      this.PclkDCAStatusSel = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCAStatusSel::type_id::create("PclkDCAStatusSel",,get_full_name());
      if(this.PclkDCAStatusSel.has_coverage(UVM_CVR_ALL))
      	this.PclkDCAStatusSel.cg_bits.option.name = {get_name(), ".", "PclkDCAStatusSel_bits"};
      this.PclkDCAStatusSel.configure(this, null, "");
      this.PclkDCAStatusSel.build();
      this.default_map.add_reg(this.PclkDCAStatusSel, `UVM_REG_ADDR_WIDTH'h511, "RW", 0);
		this.PclkDCAStatusSel_PclkDCADebugLaneSel = this.PclkDCAStatusSel.PclkDCADebugLaneSel;
		this.PclkDCADebugLaneSel = this.PclkDCAStatusSel.PclkDCADebugLaneSel;
		this.PclkDCAStatusSel_PclkDCADebugInfoSel = this.PclkDCAStatusSel.PclkDCADebugInfoSel;
		this.PclkDCADebugInfoSel = this.PclkDCAStatusSel.PclkDCADebugInfoSel;
      this.PclkDCAStatusInfo = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCAStatusInfo::type_id::create("PclkDCAStatusInfo",,get_full_name());
      if(this.PclkDCAStatusInfo.has_coverage(UVM_CVR_ALL))
      	this.PclkDCAStatusInfo.cg_bits.option.name = {get_name(), ".", "PclkDCAStatusInfo_bits"};
      this.PclkDCAStatusInfo.configure(this, null, "");
      this.PclkDCAStatusInfo.build();
      this.default_map.add_reg(this.PclkDCAStatusInfo, `UVM_REG_ADDR_WIDTH'h512, "RO", 0);
		this.PclkDCAStatusInfo_PclkDCAStatusInfo = this.PclkDCAStatusInfo.PclkDCAStatusInfo;
      this.TxDcaCtrlTTg0_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTTg0_p0::type_id::create("TxDcaCtrlTTg0_p0",,get_full_name());
      if(this.TxDcaCtrlTTg0_p0.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlTTg0_p0.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlTTg0_p0_bits"};
      this.TxDcaCtrlTTg0_p0.configure(this, null, "");
      this.TxDcaCtrlTTg0_p0.build();
      this.default_map.add_reg(this.TxDcaCtrlTTg0_p0, `UVM_REG_ADDR_WIDTH'h550, "RW", 0);
		this.TxDcaCtrlTTg0_p0_TxDcaFinePDTTg0 = this.TxDcaCtrlTTg0_p0.TxDcaFinePDTTg0;
		this.TxDcaFinePDTTg0 = this.TxDcaCtrlTTg0_p0.TxDcaFinePDTTg0;
		this.TxDcaCtrlTTg0_p0_TxDcaFinePUTTg0 = this.TxDcaCtrlTTg0_p0.TxDcaFinePUTTg0;
		this.TxDcaFinePUTTg0 = this.TxDcaCtrlTTg0_p0.TxDcaFinePUTTg0;
		this.TxDcaCtrlTTg0_p0_TxDcaCoarseTTg0 = this.TxDcaCtrlTTg0_p0.TxDcaCoarseTTg0;
		this.TxDcaCoarseTTg0 = this.TxDcaCtrlTTg0_p0.TxDcaCoarseTTg0;
      this.TxDcaCtrlTTg1_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTTg1_p0::type_id::create("TxDcaCtrlTTg1_p0",,get_full_name());
      if(this.TxDcaCtrlTTg1_p0.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlTTg1_p0.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlTTg1_p0_bits"};
      this.TxDcaCtrlTTg1_p0.configure(this, null, "");
      this.TxDcaCtrlTTg1_p0.build();
      this.default_map.add_reg(this.TxDcaCtrlTTg1_p0, `UVM_REG_ADDR_WIDTH'h551, "RW", 0);
		this.TxDcaCtrlTTg1_p0_TxDcaFinePDTTg1 = this.TxDcaCtrlTTg1_p0.TxDcaFinePDTTg1;
		this.TxDcaFinePDTTg1 = this.TxDcaCtrlTTg1_p0.TxDcaFinePDTTg1;
		this.TxDcaCtrlTTg1_p0_TxDcaFinePUTTg1 = this.TxDcaCtrlTTg1_p0.TxDcaFinePUTTg1;
		this.TxDcaFinePUTTg1 = this.TxDcaCtrlTTg1_p0.TxDcaFinePUTTg1;
		this.TxDcaCtrlTTg1_p0_TxDcaCoarseTTg1 = this.TxDcaCtrlTTg1_p0.TxDcaCoarseTTg1;
		this.TxDcaCoarseTTg1 = this.TxDcaCtrlTTg1_p0.TxDcaCoarseTTg1;
      this.TxDcaCtrlCTg0_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlCTg0_p0::type_id::create("TxDcaCtrlCTg0_p0",,get_full_name());
      if(this.TxDcaCtrlCTg0_p0.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlCTg0_p0.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlCTg0_p0_bits"};
      this.TxDcaCtrlCTg0_p0.configure(this, null, "");
      this.TxDcaCtrlCTg0_p0.build();
      this.default_map.add_reg(this.TxDcaCtrlCTg0_p0, `UVM_REG_ADDR_WIDTH'h560, "RW", 0);
		this.TxDcaCtrlCTg0_p0_TxDcaFinePDCTg0 = this.TxDcaCtrlCTg0_p0.TxDcaFinePDCTg0;
		this.TxDcaFinePDCTg0 = this.TxDcaCtrlCTg0_p0.TxDcaFinePDCTg0;
		this.TxDcaCtrlCTg0_p0_TxDcaFinePUCTg0 = this.TxDcaCtrlCTg0_p0.TxDcaFinePUCTg0;
		this.TxDcaFinePUCTg0 = this.TxDcaCtrlCTg0_p0.TxDcaFinePUCTg0;
		this.TxDcaCtrlCTg0_p0_TxDcaCoarseCTg0 = this.TxDcaCtrlCTg0_p0.TxDcaCoarseCTg0;
		this.TxDcaCoarseCTg0 = this.TxDcaCtrlCTg0_p0.TxDcaCoarseCTg0;
      this.TxDcaCtrlCTg1_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlCTg1_p0::type_id::create("TxDcaCtrlCTg1_p0",,get_full_name());
      if(this.TxDcaCtrlCTg1_p0.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlCTg1_p0.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlCTg1_p0_bits"};
      this.TxDcaCtrlCTg1_p0.configure(this, null, "");
      this.TxDcaCtrlCTg1_p0.build();
      this.default_map.add_reg(this.TxDcaCtrlCTg1_p0, `UVM_REG_ADDR_WIDTH'h561, "RW", 0);
		this.TxDcaCtrlCTg1_p0_TxDcaFinePDCTg1 = this.TxDcaCtrlCTg1_p0.TxDcaFinePDCTg1;
		this.TxDcaFinePDCTg1 = this.TxDcaCtrlCTg1_p0.TxDcaFinePDCTg1;
		this.TxDcaCtrlCTg1_p0_TxDcaFinePUCTg1 = this.TxDcaCtrlCTg1_p0.TxDcaFinePUCTg1;
		this.TxDcaFinePUCTg1 = this.TxDcaCtrlCTg1_p0.TxDcaFinePUCTg1;
		this.TxDcaCtrlCTg1_p0_TxDcaCoarseCTg1 = this.TxDcaCtrlCTg1_p0.TxDcaCoarseCTg1;
		this.TxDcaCoarseCTg1 = this.TxDcaCtrlCTg1_p0.TxDcaCoarseCTg1;
      this.RxDcaCtrlTTg0_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlTTg0_p0::type_id::create("RxDcaCtrlTTg0_p0",,get_full_name());
      if(this.RxDcaCtrlTTg0_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDcaCtrlTTg0_p0.cg_bits.option.name = {get_name(), ".", "RxDcaCtrlTTg0_p0_bits"};
      this.RxDcaCtrlTTg0_p0.configure(this, null, "");
      this.RxDcaCtrlTTg0_p0.build();
      this.default_map.add_reg(this.RxDcaCtrlTTg0_p0, `UVM_REG_ADDR_WIDTH'h570, "RW", 0);
		this.RxDcaCtrlTTg0_p0_RxDcaFinePDTTg0 = this.RxDcaCtrlTTg0_p0.RxDcaFinePDTTg0;
		this.RxDcaFinePDTTg0 = this.RxDcaCtrlTTg0_p0.RxDcaFinePDTTg0;
		this.RxDcaCtrlTTg0_p0_RxDcaFinePUTTg0 = this.RxDcaCtrlTTg0_p0.RxDcaFinePUTTg0;
		this.RxDcaFinePUTTg0 = this.RxDcaCtrlTTg0_p0.RxDcaFinePUTTg0;
		this.RxDcaCtrlTTg0_p0_RxDcaCoarseTTg0 = this.RxDcaCtrlTTg0_p0.RxDcaCoarseTTg0;
		this.RxDcaCoarseTTg0 = this.RxDcaCtrlTTg0_p0.RxDcaCoarseTTg0;
      this.RxDcaCtrlTTg1_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlTTg1_p0::type_id::create("RxDcaCtrlTTg1_p0",,get_full_name());
      if(this.RxDcaCtrlTTg1_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDcaCtrlTTg1_p0.cg_bits.option.name = {get_name(), ".", "RxDcaCtrlTTg1_p0_bits"};
      this.RxDcaCtrlTTg1_p0.configure(this, null, "");
      this.RxDcaCtrlTTg1_p0.build();
      this.default_map.add_reg(this.RxDcaCtrlTTg1_p0, `UVM_REG_ADDR_WIDTH'h571, "RW", 0);
		this.RxDcaCtrlTTg1_p0_RxDcaFinePDTTg1 = this.RxDcaCtrlTTg1_p0.RxDcaFinePDTTg1;
		this.RxDcaFinePDTTg1 = this.RxDcaCtrlTTg1_p0.RxDcaFinePDTTg1;
		this.RxDcaCtrlTTg1_p0_RxDcaFinePUTTg1 = this.RxDcaCtrlTTg1_p0.RxDcaFinePUTTg1;
		this.RxDcaFinePUTTg1 = this.RxDcaCtrlTTg1_p0.RxDcaFinePUTTg1;
		this.RxDcaCtrlTTg1_p0_RxDcaCoarseTTg1 = this.RxDcaCtrlTTg1_p0.RxDcaCoarseTTg1;
		this.RxDcaCoarseTTg1 = this.RxDcaCtrlTTg1_p0.RxDcaCoarseTTg1;
      this.RxDcaCtrlCTg0_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlCTg0_p0::type_id::create("RxDcaCtrlCTg0_p0",,get_full_name());
      if(this.RxDcaCtrlCTg0_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDcaCtrlCTg0_p0.cg_bits.option.name = {get_name(), ".", "RxDcaCtrlCTg0_p0_bits"};
      this.RxDcaCtrlCTg0_p0.configure(this, null, "");
      this.RxDcaCtrlCTg0_p0.build();
      this.default_map.add_reg(this.RxDcaCtrlCTg0_p0, `UVM_REG_ADDR_WIDTH'h580, "RW", 0);
		this.RxDcaCtrlCTg0_p0_RxDcaFinePDCTg0 = this.RxDcaCtrlCTg0_p0.RxDcaFinePDCTg0;
		this.RxDcaFinePDCTg0 = this.RxDcaCtrlCTg0_p0.RxDcaFinePDCTg0;
		this.RxDcaCtrlCTg0_p0_RxDcaFinePUCTg0 = this.RxDcaCtrlCTg0_p0.RxDcaFinePUCTg0;
		this.RxDcaFinePUCTg0 = this.RxDcaCtrlCTg0_p0.RxDcaFinePUCTg0;
		this.RxDcaCtrlCTg0_p0_RxDcaCoarseCTg0 = this.RxDcaCtrlCTg0_p0.RxDcaCoarseCTg0;
		this.RxDcaCoarseCTg0 = this.RxDcaCtrlCTg0_p0.RxDcaCoarseCTg0;
      this.RxDcaCtrlCTg1_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxDcaCtrlCTg1_p0::type_id::create("RxDcaCtrlCTg1_p0",,get_full_name());
      if(this.RxDcaCtrlCTg1_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDcaCtrlCTg1_p0.cg_bits.option.name = {get_name(), ".", "RxDcaCtrlCTg1_p0_bits"};
      this.RxDcaCtrlCTg1_p0.configure(this, null, "");
      this.RxDcaCtrlCTg1_p0.build();
      this.default_map.add_reg(this.RxDcaCtrlCTg1_p0, `UVM_REG_ADDR_WIDTH'h581, "RW", 0);
		this.RxDcaCtrlCTg1_p0_RxDcaFinePDCTg1 = this.RxDcaCtrlCTg1_p0.RxDcaFinePDCTg1;
		this.RxDcaFinePDCTg1 = this.RxDcaCtrlCTg1_p0.RxDcaFinePDCTg1;
		this.RxDcaCtrlCTg1_p0_RxDcaFinePUCTg1 = this.RxDcaCtrlCTg1_p0.RxDcaFinePUCTg1;
		this.RxDcaFinePUCTg1 = this.RxDcaCtrlCTg1_p0.RxDcaFinePUCTg1;
		this.RxDcaCtrlCTg1_p0_RxDcaCoarseCTg1 = this.RxDcaCtrlCTg1_p0.RxDcaCoarseCTg1;
		this.RxDcaCoarseCTg1 = this.RxDcaCtrlCTg1_p0.RxDcaCoarseCTg1;
      this.PclkDCALcdlCalCtrl = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCALcdlCalCtrl::type_id::create("PclkDCALcdlCalCtrl",,get_full_name());
      if(this.PclkDCALcdlCalCtrl.has_coverage(UVM_CVR_ALL))
      	this.PclkDCALcdlCalCtrl.cg_bits.option.name = {get_name(), ".", "PclkDCALcdlCalCtrl_bits"};
      this.PclkDCALcdlCalCtrl.configure(this, null, "");
      this.PclkDCALcdlCalCtrl.build();
      this.default_map.add_reg(this.PclkDCALcdlCalCtrl, `UVM_REG_ADDR_WIDTH'h591, "RW", 0);
		this.PclkDCALcdlCalCtrl_PclkDCAUseCSRForCalCtrl = this.PclkDCALcdlCalCtrl.PclkDCAUseCSRForCalCtrl;
		this.PclkDCAUseCSRForCalCtrl = this.PclkDCALcdlCalCtrl.PclkDCAUseCSRForCalCtrl;
		this.PclkDCALcdlCalCtrl_PclkDCALcdlCalMode = this.PclkDCALcdlCalCtrl.PclkDCALcdlCalMode;
		this.PclkDCALcdlCalMode = this.PclkDCALcdlCalCtrl.PclkDCALcdlCalMode;
		this.PclkDCALcdlCalCtrl_PclkDCALcdlCalEn = this.PclkDCALcdlCalCtrl.PclkDCALcdlCalEn;
		this.PclkDCALcdlCalEn = this.PclkDCALcdlCalCtrl.PclkDCALcdlCalEn;
		this.PclkDCALcdlCalCtrl_PclkDCALcdlCalPhaseUpdate = this.PclkDCALcdlCalCtrl.PclkDCALcdlCalPhaseUpdate;
		this.PclkDCALcdlCalPhaseUpdate = this.PclkDCALcdlCalCtrl.PclkDCALcdlCalPhaseUpdate;
		this.PclkDCALcdlCalCtrl_PclkDCALcdlCalClkEn = this.PclkDCALcdlCalCtrl.PclkDCALcdlCalClkEn;
		this.PclkDCALcdlCalClkEn = this.PclkDCALcdlCalCtrl.PclkDCALcdlCalClkEn;
		this.PclkDCALcdlCalCtrl_PclkDCALcdlCalSampEn = this.PclkDCALcdlCalCtrl.PclkDCALcdlCalSampEn;
		this.PclkDCALcdlCalSampEn = this.PclkDCALcdlCalCtrl.PclkDCALcdlCalSampEn;
		this.PclkDCALcdlCalCtrl_PclkDCALcdlResetRelock = this.PclkDCALcdlCalCtrl.PclkDCALcdlResetRelock;
		this.PclkDCALcdlResetRelock = this.PclkDCALcdlCalCtrl.PclkDCALcdlResetRelock;
		this.PclkDCALcdlCalCtrl_PclkDCALcdlStopCal = this.PclkDCALcdlCalCtrl.PclkDCALcdlStopCal;
		this.PclkDCALcdlStopCal = this.PclkDCALcdlCalCtrl.PclkDCALcdlStopCal;
      this.DlyTestCntDfiClkIVHM = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntDfiClkIVHM::type_id::create("DlyTestCntDfiClkIVHM",,get_full_name());
      if(this.DlyTestCntDfiClkIVHM.has_coverage(UVM_CVR_ALL))
      	this.DlyTestCntDfiClkIVHM.cg_bits.option.name = {get_name(), ".", "DlyTestCntDfiClkIVHM_bits"};
      this.DlyTestCntDfiClkIVHM.configure(this, null, "");
      this.DlyTestCntDfiClkIVHM.build();
      this.default_map.add_reg(this.DlyTestCntDfiClkIVHM, `UVM_REG_ADDR_WIDTH'h5D3, "RW", 0);
		this.DlyTestCntDfiClkIVHM_DlyTestCntDfiClkIVHM = this.DlyTestCntDfiClkIVHM.DlyTestCntDfiClkIVHM;
      this.DlyTestCntDfiClkHM = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntDfiClkHM::type_id::create("DlyTestCntDfiClkHM",,get_full_name());
      if(this.DlyTestCntDfiClkHM.has_coverage(UVM_CVR_ALL))
      	this.DlyTestCntDfiClkHM.cg_bits.option.name = {get_name(), ".", "DlyTestCntDfiClkHM_bits"};
      this.DlyTestCntDfiClkHM.configure(this, null, "");
      this.DlyTestCntDfiClkHM.build();
      this.default_map.add_reg(this.DlyTestCntDfiClkHM, `UVM_REG_ADDR_WIDTH'h5D4, "RO", 0);
		this.DlyTestCntDfiClkHM_DlyTestCntDfiClkHM = this.DlyTestCntDfiClkHM.DlyTestCntDfiClkHM;
      this.DlyTestCntRingOsc = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntRingOsc::type_id::create("DlyTestCntRingOsc",,get_full_name());
      if(this.DlyTestCntRingOsc.has_coverage(UVM_CVR_ALL))
      	this.DlyTestCntRingOsc.cg_bits.option.name = {get_name(), ".", "DlyTestCntRingOsc_bits"};
      this.DlyTestCntRingOsc.configure(this, null, "");
      this.DlyTestCntRingOsc.build();
      this.default_map.add_reg(this.DlyTestCntRingOsc, `UVM_REG_ADDR_WIDTH'h5D5, "RO", 0);
		this.DlyTestCntRingOsc_DlyTestCntRingOsc = this.DlyTestCntRingOsc.DlyTestCntRingOsc;
      this.DlyTestSeqHM = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestSeqHM::type_id::create("DlyTestSeqHM",,get_full_name());
      if(this.DlyTestSeqHM.has_coverage(UVM_CVR_ALL))
      	this.DlyTestSeqHM.cg_bits.option.name = {get_name(), ".", "DlyTestSeqHM_bits"};
      this.DlyTestSeqHM.configure(this, null, "");
      this.DlyTestSeqHM.build();
      this.default_map.add_reg(this.DlyTestSeqHM, `UVM_REG_ADDR_WIDTH'h5DF, "RW", 0);
		this.DlyTestSeqHM_DlyTestSeqHM = this.DlyTestSeqHM.DlyTestSeqHM;
      this.PclkDCALcdlAddDlySampEn_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkDCALcdlAddDlySampEn_p0::type_id::create("PclkDCALcdlAddDlySampEn_p0",,get_full_name());
      if(this.PclkDCALcdlAddDlySampEn_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCALcdlAddDlySampEn_p0.cg_bits.option.name = {get_name(), ".", "PclkDCALcdlAddDlySampEn_p0_bits"};
      this.PclkDCALcdlAddDlySampEn_p0.configure(this, null, "");
      this.PclkDCALcdlAddDlySampEn_p0.build();
      this.default_map.add_reg(this.PclkDCALcdlAddDlySampEn_p0, `UVM_REG_ADDR_WIDTH'h5E3, "RW", 0);
		this.PclkDCALcdlAddDlySampEn_p0_PclkDCALcdlAddDlySampEn_p0 = this.PclkDCALcdlAddDlySampEn_p0.PclkDCALcdlAddDlySampEn_p0;
      this.PclkEnDQSIO = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_PclkEnDQSIO::type_id::create("PclkEnDQSIO",,get_full_name());
      if(this.PclkEnDQSIO.has_coverage(UVM_CVR_ALL))
      	this.PclkEnDQSIO.cg_bits.option.name = {get_name(), ".", "PclkEnDQSIO_bits"};
      this.PclkEnDQSIO.configure(this, null, "");
      this.PclkEnDQSIO.build();
      this.default_map.add_reg(this.PclkEnDQSIO, `UVM_REG_ADDR_WIDTH'h5E4, "RW", 0);
		this.PclkEnDQSIO_PclkEnDQSIO = this.PclkEnDQSIO.PclkEnDQSIO;
      this.TxDcaCtrlTg0Ln0_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln0_p0::type_id::create("TxDcaCtrlTg0Ln0_p0",,get_full_name());
      if(this.TxDcaCtrlTg0Ln0_p0.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlTg0Ln0_p0.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlTg0Ln0_p0_bits"};
      this.TxDcaCtrlTg0Ln0_p0.configure(this, null, "");
      this.TxDcaCtrlTg0Ln0_p0.build();
      this.default_map.add_reg(this.TxDcaCtrlTg0Ln0_p0, `UVM_REG_ADDR_WIDTH'h600, "RW", 0);
		this.TxDcaCtrlTg0Ln0_p0_TxDcaCoarseTg0Ln0 = this.TxDcaCtrlTg0Ln0_p0.TxDcaCoarseTg0Ln0;
		this.TxDcaCoarseTg0Ln0 = this.TxDcaCtrlTg0Ln0_p0.TxDcaCoarseTg0Ln0;
		this.TxDcaCtrlTg0Ln0_p0_TxDcaFinePUTg0Ln0 = this.TxDcaCtrlTg0Ln0_p0.TxDcaFinePUTg0Ln0;
		this.TxDcaFinePUTg0Ln0 = this.TxDcaCtrlTg0Ln0_p0.TxDcaFinePUTg0Ln0;
		this.TxDcaCtrlTg0Ln0_p0_TxDcaFinePDTg0Ln0 = this.TxDcaCtrlTg0Ln0_p0.TxDcaFinePDTg0Ln0;
		this.TxDcaFinePDTg0Ln0 = this.TxDcaCtrlTg0Ln0_p0.TxDcaFinePDTg0Ln0;
      this.TxDcaCtrlTg1Ln0_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln0_p0::type_id::create("TxDcaCtrlTg1Ln0_p0",,get_full_name());
      if(this.TxDcaCtrlTg1Ln0_p0.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlTg1Ln0_p0.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlTg1Ln0_p0_bits"};
      this.TxDcaCtrlTg1Ln0_p0.configure(this, null, "");
      this.TxDcaCtrlTg1Ln0_p0.build();
      this.default_map.add_reg(this.TxDcaCtrlTg1Ln0_p0, `UVM_REG_ADDR_WIDTH'h601, "RW", 0);
		this.TxDcaCtrlTg1Ln0_p0_TxDcaCoarseTg1Ln0 = this.TxDcaCtrlTg1Ln0_p0.TxDcaCoarseTg1Ln0;
		this.TxDcaCoarseTg1Ln0 = this.TxDcaCtrlTg1Ln0_p0.TxDcaCoarseTg1Ln0;
		this.TxDcaCtrlTg1Ln0_p0_TxDcaFinePUTg1Ln0 = this.TxDcaCtrlTg1Ln0_p0.TxDcaFinePUTg1Ln0;
		this.TxDcaFinePUTg1Ln0 = this.TxDcaCtrlTg1Ln0_p0.TxDcaFinePUTg1Ln0;
		this.TxDcaCtrlTg1Ln0_p0_TxDcaFinePDTg1Ln0 = this.TxDcaCtrlTg1Ln0_p0.TxDcaFinePDTg1Ln0;
		this.TxDcaFinePDTg1Ln0 = this.TxDcaCtrlTg1Ln0_p0.TxDcaFinePDTg1Ln0;
      this.TxDcaCtrlTg0Ln1_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln1_p0::type_id::create("TxDcaCtrlTg0Ln1_p0",,get_full_name());
      if(this.TxDcaCtrlTg0Ln1_p0.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlTg0Ln1_p0.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlTg0Ln1_p0_bits"};
      this.TxDcaCtrlTg0Ln1_p0.configure(this, null, "");
      this.TxDcaCtrlTg0Ln1_p0.build();
      this.default_map.add_reg(this.TxDcaCtrlTg0Ln1_p0, `UVM_REG_ADDR_WIDTH'h610, "RW", 0);
		this.TxDcaCtrlTg0Ln1_p0_TxDcaCoarseTg0Ln1 = this.TxDcaCtrlTg0Ln1_p0.TxDcaCoarseTg0Ln1;
		this.TxDcaCoarseTg0Ln1 = this.TxDcaCtrlTg0Ln1_p0.TxDcaCoarseTg0Ln1;
		this.TxDcaCtrlTg0Ln1_p0_TxDcaFinePUTg0Ln1 = this.TxDcaCtrlTg0Ln1_p0.TxDcaFinePUTg0Ln1;
		this.TxDcaFinePUTg0Ln1 = this.TxDcaCtrlTg0Ln1_p0.TxDcaFinePUTg0Ln1;
		this.TxDcaCtrlTg0Ln1_p0_TxDcaFinePDTg0Ln1 = this.TxDcaCtrlTg0Ln1_p0.TxDcaFinePDTg0Ln1;
		this.TxDcaFinePDTg0Ln1 = this.TxDcaCtrlTg0Ln1_p0.TxDcaFinePDTg0Ln1;
      this.TxDcaCtrlTg1Ln1_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln1_p0::type_id::create("TxDcaCtrlTg1Ln1_p0",,get_full_name());
      if(this.TxDcaCtrlTg1Ln1_p0.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlTg1Ln1_p0.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlTg1Ln1_p0_bits"};
      this.TxDcaCtrlTg1Ln1_p0.configure(this, null, "");
      this.TxDcaCtrlTg1Ln1_p0.build();
      this.default_map.add_reg(this.TxDcaCtrlTg1Ln1_p0, `UVM_REG_ADDR_WIDTH'h611, "RW", 0);
		this.TxDcaCtrlTg1Ln1_p0_TxDcaCoarseTg1Ln1 = this.TxDcaCtrlTg1Ln1_p0.TxDcaCoarseTg1Ln1;
		this.TxDcaCoarseTg1Ln1 = this.TxDcaCtrlTg1Ln1_p0.TxDcaCoarseTg1Ln1;
		this.TxDcaCtrlTg1Ln1_p0_TxDcaFinePUTg1Ln1 = this.TxDcaCtrlTg1Ln1_p0.TxDcaFinePUTg1Ln1;
		this.TxDcaFinePUTg1Ln1 = this.TxDcaCtrlTg1Ln1_p0.TxDcaFinePUTg1Ln1;
		this.TxDcaCtrlTg1Ln1_p0_TxDcaFinePDTg1Ln1 = this.TxDcaCtrlTg1Ln1_p0.TxDcaFinePDTg1Ln1;
		this.TxDcaFinePDTg1Ln1 = this.TxDcaCtrlTg1Ln1_p0.TxDcaFinePDTg1Ln1;
      this.TxDcaCtrlTg0Ln2_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln2_p0::type_id::create("TxDcaCtrlTg0Ln2_p0",,get_full_name());
      if(this.TxDcaCtrlTg0Ln2_p0.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlTg0Ln2_p0.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlTg0Ln2_p0_bits"};
      this.TxDcaCtrlTg0Ln2_p0.configure(this, null, "");
      this.TxDcaCtrlTg0Ln2_p0.build();
      this.default_map.add_reg(this.TxDcaCtrlTg0Ln2_p0, `UVM_REG_ADDR_WIDTH'h620, "RW", 0);
		this.TxDcaCtrlTg0Ln2_p0_TxDcaCoarseTg0Ln2 = this.TxDcaCtrlTg0Ln2_p0.TxDcaCoarseTg0Ln2;
		this.TxDcaCoarseTg0Ln2 = this.TxDcaCtrlTg0Ln2_p0.TxDcaCoarseTg0Ln2;
		this.TxDcaCtrlTg0Ln2_p0_TxDcaFinePUTg0Ln2 = this.TxDcaCtrlTg0Ln2_p0.TxDcaFinePUTg0Ln2;
		this.TxDcaFinePUTg0Ln2 = this.TxDcaCtrlTg0Ln2_p0.TxDcaFinePUTg0Ln2;
		this.TxDcaCtrlTg0Ln2_p0_TxDcaFinePDTg0Ln2 = this.TxDcaCtrlTg0Ln2_p0.TxDcaFinePDTg0Ln2;
		this.TxDcaFinePDTg0Ln2 = this.TxDcaCtrlTg0Ln2_p0.TxDcaFinePDTg0Ln2;
      this.TxDcaCtrlTg1Ln2_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln2_p0::type_id::create("TxDcaCtrlTg1Ln2_p0",,get_full_name());
      if(this.TxDcaCtrlTg1Ln2_p0.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlTg1Ln2_p0.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlTg1Ln2_p0_bits"};
      this.TxDcaCtrlTg1Ln2_p0.configure(this, null, "");
      this.TxDcaCtrlTg1Ln2_p0.build();
      this.default_map.add_reg(this.TxDcaCtrlTg1Ln2_p0, `UVM_REG_ADDR_WIDTH'h621, "RW", 0);
		this.TxDcaCtrlTg1Ln2_p0_TxDcaCoarseTg1Ln2 = this.TxDcaCtrlTg1Ln2_p0.TxDcaCoarseTg1Ln2;
		this.TxDcaCoarseTg1Ln2 = this.TxDcaCtrlTg1Ln2_p0.TxDcaCoarseTg1Ln2;
		this.TxDcaCtrlTg1Ln2_p0_TxDcaFinePUTg1Ln2 = this.TxDcaCtrlTg1Ln2_p0.TxDcaFinePUTg1Ln2;
		this.TxDcaFinePUTg1Ln2 = this.TxDcaCtrlTg1Ln2_p0.TxDcaFinePUTg1Ln2;
		this.TxDcaCtrlTg1Ln2_p0_TxDcaFinePDTg1Ln2 = this.TxDcaCtrlTg1Ln2_p0.TxDcaFinePDTg1Ln2;
		this.TxDcaFinePDTg1Ln2 = this.TxDcaCtrlTg1Ln2_p0.TxDcaFinePDTg1Ln2;
      this.TxDcaCtrlTg0Ln3_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg0Ln3_p0::type_id::create("TxDcaCtrlTg0Ln3_p0",,get_full_name());
      if(this.TxDcaCtrlTg0Ln3_p0.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlTg0Ln3_p0.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlTg0Ln3_p0_bits"};
      this.TxDcaCtrlTg0Ln3_p0.configure(this, null, "");
      this.TxDcaCtrlTg0Ln3_p0.build();
      this.default_map.add_reg(this.TxDcaCtrlTg0Ln3_p0, `UVM_REG_ADDR_WIDTH'h630, "RW", 0);
		this.TxDcaCtrlTg0Ln3_p0_TxDcaCoarseTg0Ln3 = this.TxDcaCtrlTg0Ln3_p0.TxDcaCoarseTg0Ln3;
		this.TxDcaCoarseTg0Ln3 = this.TxDcaCtrlTg0Ln3_p0.TxDcaCoarseTg0Ln3;
		this.TxDcaCtrlTg0Ln3_p0_TxDcaFinePUTg0Ln3 = this.TxDcaCtrlTg0Ln3_p0.TxDcaFinePUTg0Ln3;
		this.TxDcaFinePUTg0Ln3 = this.TxDcaCtrlTg0Ln3_p0.TxDcaFinePUTg0Ln3;
		this.TxDcaCtrlTg0Ln3_p0_TxDcaFinePDTg0Ln3 = this.TxDcaCtrlTg0Ln3_p0.TxDcaFinePDTg0Ln3;
		this.TxDcaFinePDTg0Ln3 = this.TxDcaCtrlTg0Ln3_p0.TxDcaFinePDTg0Ln3;
      this.TxDcaCtrlTg1Ln3_p0 = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_TxDcaCtrlTg1Ln3_p0::type_id::create("TxDcaCtrlTg1Ln3_p0",,get_full_name());
      if(this.TxDcaCtrlTg1Ln3_p0.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlTg1Ln3_p0.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlTg1Ln3_p0_bits"};
      this.TxDcaCtrlTg1Ln3_p0.configure(this, null, "");
      this.TxDcaCtrlTg1Ln3_p0.build();
      this.default_map.add_reg(this.TxDcaCtrlTg1Ln3_p0, `UVM_REG_ADDR_WIDTH'h631, "RW", 0);
		this.TxDcaCtrlTg1Ln3_p0_TxDcaCoarseTg1Ln3 = this.TxDcaCtrlTg1Ln3_p0.TxDcaCoarseTg1Ln3;
		this.TxDcaCoarseTg1Ln3 = this.TxDcaCtrlTg1Ln3_p0.TxDcaCoarseTg1Ln3;
		this.TxDcaCtrlTg1Ln3_p0_TxDcaFinePUTg1Ln3 = this.TxDcaCtrlTg1Ln3_p0.TxDcaFinePUTg1Ln3;
		this.TxDcaFinePUTg1Ln3 = this.TxDcaCtrlTg1Ln3_p0.TxDcaFinePUTg1Ln3;
		this.TxDcaCtrlTg1Ln3_p0_TxDcaFinePDTg1Ln3 = this.TxDcaCtrlTg1Ln3_p0.TxDcaFinePDTg1Ln3;
		this.TxDcaFinePDTg1Ln3 = this.TxDcaCtrlTg1Ln3_p0.TxDcaFinePDTg1Ln3;
      this.RxReplicaLcdlStatus = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_RxReplicaLcdlStatus::type_id::create("RxReplicaLcdlStatus",,get_full_name());
      if(this.RxReplicaLcdlStatus.has_coverage(UVM_CVR_ALL))
      	this.RxReplicaLcdlStatus.cg_bits.option.name = {get_name(), ".", "RxReplicaLcdlStatus_bits"};
      this.RxReplicaLcdlStatus.configure(this, null, "");
      this.RxReplicaLcdlStatus.build();
      this.default_map.add_reg(this.RxReplicaLcdlStatus, `UVM_REG_ADDR_WIDTH'h67C, "RO", 0);
		this.RxReplicaLcdlStatus_RxReplicaLcdlFineSnapVal = this.RxReplicaLcdlStatus.RxReplicaLcdlFineSnapVal;
		this.RxReplicaLcdlFineSnapVal = this.RxReplicaLcdlStatus.RxReplicaLcdlFineSnapVal;
      this.DlyTestCntRingOscSelDX = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestCntRingOscSelDX::type_id::create("DlyTestCntRingOscSelDX",,get_full_name());
      if(this.DlyTestCntRingOscSelDX.has_coverage(UVM_CVR_ALL))
      	this.DlyTestCntRingOscSelDX.cg_bits.option.name = {get_name(), ".", "DlyTestCntRingOscSelDX_bits"};
      this.DlyTestCntRingOscSelDX.configure(this, null, "");
      this.DlyTestCntRingOscSelDX.build();
      this.default_map.add_reg(this.DlyTestCntRingOscSelDX, `UVM_REG_ADDR_WIDTH'h692, "RW", 0);
		this.DlyTestCntRingOscSelDX_DlyTestCntRingOscSelDX = this.DlyTestCntRingOscSelDX.DlyTestCntRingOscSelDX;
      this.DlyTestRingSelDX = ral_reg_DWC_DDRPHYA_HMDBYTE4_4_p0_DlyTestRingSelDX::type_id::create("DlyTestRingSelDX",,get_full_name());
      if(this.DlyTestRingSelDX.has_coverage(UVM_CVR_ALL))
      	this.DlyTestRingSelDX.cg_bits.option.name = {get_name(), ".", "DlyTestRingSelDX_bits"};
      this.DlyTestRingSelDX.configure(this, null, "");
      this.DlyTestRingSelDX.build();
      this.default_map.add_reg(this.DlyTestRingSelDX, `UVM_REG_ADDR_WIDTH'h6D1, "RW", 0);
		this.DlyTestRingSelDX_DlyTestRingSelDX = this.DlyTestRingSelDX.DlyTestRingSelDX;
   endfunction : build

	`uvm_object_utils(ral_block_DWC_DDRPHYA_HMDBYTE4_4_p0)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_DDRPHYA_HMDBYTE4_4_p0


endpackage
`endif
