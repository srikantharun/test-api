`ifndef RAL_DWC_DDRPHYA_AC0_P3_PKG
`define RAL_DWC_DDRPHYA_AC0_P3_PKG

package ral_DWC_DDRPHYA_AC0_p3_pkg;
import uvm_pkg::*;

class ral_reg_DWC_DDRPHYA_AC0_p3_AcPipeEn_p3 extends uvm_reg;
	rand uvm_reg_field AcPipeEn_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcPipeEn_p3: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_AcPipeEn_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcPipeEn_p3 = uvm_reg_field::type_id::create("AcPipeEn_p3",,get_full_name());
      this.AcPipeEn_p3.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_AcPipeEn_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_AcPipeEn_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_CkVal_p3 extends uvm_reg;
	rand uvm_reg_field CkVal_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CkVal_p3: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_CkVal_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CkVal_p3 = uvm_reg_field::type_id::create("CkVal_p3",,get_full_name());
      this.CkVal_p3.configure(this, 2, 0, "RW", 0, 2'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_CkVal_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_CkVal_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_CkDisVal_p3 extends uvm_reg;
	uvm_reg_field Reserved;
	rand uvm_reg_field CkDisVal_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   Reserved: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   CkDisVal_p3: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC0_p3_CkDisVal_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.Reserved = uvm_reg_field::type_id::create("Reserved",,get_full_name());
      this.Reserved.configure(this, 1, 0, "RO", 1, 1'h0, 1, 0, 0);
      this.CkDisVal_p3 = uvm_reg_field::type_id::create("CkDisVal_p3",,get_full_name());
      this.CkDisVal_p3.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_CkDisVal_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_CkDisVal_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACSingleEndedMode_p3 extends uvm_reg;
	rand uvm_reg_field SingleEndedCK;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   SingleEndedCK: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACSingleEndedMode_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.SingleEndedCK = uvm_reg_field::type_id::create("SingleEndedCK",,get_full_name());
      this.SingleEndedCK.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACSingleEndedMode_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACSingleEndedMode_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_RxAcVrefControl_p3 extends uvm_reg;
	rand uvm_reg_field RxAcVrefDac;
	rand uvm_reg_field RxAcVrefDacEn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxAcVrefDac: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	   RxAcVrefDacEn: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC0_p3_RxAcVrefControl_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxAcVrefDac = uvm_reg_field::type_id::create("RxAcVrefDac",,get_full_name());
      this.RxAcVrefDac.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
      this.RxAcVrefDacEn = uvm_reg_field::type_id::create("RxAcVrefDacEn",,get_full_name());
      this.RxAcVrefDacEn.configure(this, 1, 8, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_RxAcVrefControl_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_RxAcVrefControl_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ATxDlySelect_p3 extends uvm_reg;
	rand uvm_reg_field ATxDlySelect_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ATxDlySelect_p3: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ATxDlySelect_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ATxDlySelect_p3 = uvm_reg_field::type_id::create("ATxDlySelect_p3",,get_full_name());
      this.ATxDlySelect_p3.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ATxDlySelect_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ATxDlySelect_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r0_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDly_r0_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly_r0_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDly_r0_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly_r0_p3 = uvm_reg_field::type_id::create("ACXTxDly_r0_p3",,get_full_name());
      this.ACXTxDly_r0_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r0_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r0_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_CKXTxDly_p3 extends uvm_reg;
	rand uvm_reg_field CKXTxDly_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CKXTxDly_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_CKXTxDly_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CKXTxDly_p3 = uvm_reg_field::type_id::create("CKXTxDly_p3",,get_full_name());
      this.CKXTxDly_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_CKXTxDly_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_CKXTxDly_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDlyDTO_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDlyDTO_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDlyDTO_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDlyDTO_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDlyDTO_p3 = uvm_reg_field::type_id::create("ACXTxDlyDTO_p3",,get_full_name());
      this.ACXTxDlyDTO_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDlyDTO_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDlyDTO_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r0_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDly2nMode_r0_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly2nMode_r0_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r0_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly2nMode_r0_p3 = uvm_reg_field::type_id::create("ACXTxDly2nMode_r0_p3",,get_full_name());
      this.ACXTxDly2nMode_r0_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r0_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r0_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_AcLcdlUpdInterval_p3 extends uvm_reg;
	rand uvm_reg_field AcLcdlUpdInterval_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcLcdlUpdInterval_p3: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_AcLcdlUpdInterval_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcLcdlUpdInterval_p3 = uvm_reg_field::type_id::create("AcLcdlUpdInterval_p3",,get_full_name());
      this.AcLcdlUpdInterval_p3.configure(this, 16, 0, "RW", 0, 16'h80, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_AcLcdlUpdInterval_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_AcLcdlUpdInterval_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_LcdlCalSeqUpdCK_p3 extends uvm_reg;
	rand uvm_reg_field LcdlCalSeqUpdCK_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   LcdlCalSeqUpdCK_p3: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_LcdlCalSeqUpdCK_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.LcdlCalSeqUpdCK_p3 = uvm_reg_field::type_id::create("LcdlCalSeqUpdCK_p3",,get_full_name());
      this.LcdlCalSeqUpdCK_p3.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_LcdlCalSeqUpdCK_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_LcdlCalSeqUpdCK_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_PUBReservedP1_p3 extends uvm_reg;
	rand uvm_reg_field PUBReservedP1_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PUBReservedP1_p3: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_PUBReservedP1_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PUBReservedP1_p3 = uvm_reg_field::type_id::create("PUBReservedP1_p3",,get_full_name());
      this.PUBReservedP1_p3.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_PUBReservedP1_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_PUBReservedP1_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_PclkDCDCtrl_p3 extends uvm_reg;
	rand uvm_reg_field PclkDCDEn;
	rand uvm_reg_field PclkDCDOffsetMode;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCDEn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PclkDCDOffsetMode: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC0_p3_PclkDCDCtrl_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCDEn = uvm_reg_field::type_id::create("PclkDCDEn",,get_full_name());
      this.PclkDCDEn.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.PclkDCDOffsetMode = uvm_reg_field::type_id::create("PclkDCDOffsetMode",,get_full_name());
      this.PclkDCDOffsetMode.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_PclkDCDCtrl_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_PclkDCDCtrl_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r1_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDly_r1_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly_r1_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDly_r1_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly_r1_p3 = uvm_reg_field::type_id::create("ACXTxDly_r1_p3",,get_full_name());
      this.ACXTxDly_r1_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r1_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r1_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r1_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDly2nMode_r1_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly2nMode_r1_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r1_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly2nMode_r1_p3 = uvm_reg_field::type_id::create("ACXTxDly2nMode_r1_p3",,get_full_name());
      this.ACXTxDly2nMode_r1_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r1_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r1_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r2_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDly_r2_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly_r2_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDly_r2_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly_r2_p3 = uvm_reg_field::type_id::create("ACXTxDly_r2_p3",,get_full_name());
      this.ACXTxDly_r2_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r2_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r2_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r2_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDly2nMode_r2_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly2nMode_r2_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r2_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly2nMode_r2_p3 = uvm_reg_field::type_id::create("ACXTxDly2nMode_r2_p3",,get_full_name());
      this.ACXTxDly2nMode_r2_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r2_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r2_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r3_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDly_r3_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly_r3_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDly_r3_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly_r3_p3 = uvm_reg_field::type_id::create("ACXTxDly_r3_p3",,get_full_name());
      this.ACXTxDly_r3_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r3_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r3_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r3_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDly2nMode_r3_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly2nMode_r3_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r3_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly2nMode_r3_p3 = uvm_reg_field::type_id::create("ACXTxDly2nMode_r3_p3",,get_full_name());
      this.ACXTxDly2nMode_r3_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r3_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r3_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r4_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDly_r4_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly_r4_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDly_r4_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly_r4_p3 = uvm_reg_field::type_id::create("ACXTxDly_r4_p3",,get_full_name());
      this.ACXTxDly_r4_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r4_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r4_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r4_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDly2nMode_r4_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly2nMode_r4_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r4_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly2nMode_r4_p3 = uvm_reg_field::type_id::create("ACXTxDly2nMode_r4_p3",,get_full_name());
      this.ACXTxDly2nMode_r4_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r4_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r4_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r5_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDly_r5_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly_r5_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDly_r5_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly_r5_p3 = uvm_reg_field::type_id::create("ACXTxDly_r5_p3",,get_full_name());
      this.ACXTxDly_r5_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r5_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r5_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r5_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDly2nMode_r5_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly2nMode_r5_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r5_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly2nMode_r5_p3 = uvm_reg_field::type_id::create("ACXTxDly2nMode_r5_p3",,get_full_name());
      this.ACXTxDly2nMode_r5_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r5_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r5_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r6_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDly_r6_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly_r6_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDly_r6_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly_r6_p3 = uvm_reg_field::type_id::create("ACXTxDly_r6_p3",,get_full_name());
      this.ACXTxDly_r6_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r6_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r6_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r6_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDly2nMode_r6_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly2nMode_r6_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r6_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly2nMode_r6_p3 = uvm_reg_field::type_id::create("ACXTxDly2nMode_r6_p3",,get_full_name());
      this.ACXTxDly2nMode_r6_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r6_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r6_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r7_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDly_r7_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly_r7_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDly_r7_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly_r7_p3 = uvm_reg_field::type_id::create("ACXTxDly_r7_p3",,get_full_name());
      this.ACXTxDly_r7_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r7_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r7_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r7_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDly2nMode_r7_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly2nMode_r7_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r7_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly2nMode_r7_p3 = uvm_reg_field::type_id::create("ACXTxDly2nMode_r7_p3",,get_full_name());
      this.ACXTxDly2nMode_r7_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r7_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r7_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_PclkDCAStaticCtrl0AC_p3 extends uvm_reg;
	rand uvm_reg_field PclkDCACalModeAC;
	rand uvm_reg_field PclkDCAEnAC;
	rand uvm_reg_field PclkDCATxLcdlPhSelAC;
	rand uvm_reg_field PclkDCDSettleAC;
	rand uvm_reg_field PclkDCDSampTimeAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACalModeAC: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PclkDCAEnAC: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PclkDCATxLcdlPhSelAC: coverpoint {m_data[3:2], m_is_read} iff(m_be) {
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
	   PclkDCDSettleAC: coverpoint {m_data[10:4], m_is_read} iff(m_be) {
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
	   PclkDCDSampTimeAC: coverpoint {m_data[14:11], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_PclkDCAStaticCtrl0AC_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACalModeAC = uvm_reg_field::type_id::create("PclkDCACalModeAC",,get_full_name());
      this.PclkDCACalModeAC.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.PclkDCAEnAC = uvm_reg_field::type_id::create("PclkDCAEnAC",,get_full_name());
      this.PclkDCAEnAC.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.PclkDCATxLcdlPhSelAC = uvm_reg_field::type_id::create("PclkDCATxLcdlPhSelAC",,get_full_name());
      this.PclkDCATxLcdlPhSelAC.configure(this, 2, 2, "RW", 0, 2'h0, 1, 0, 0);
      this.PclkDCDSettleAC = uvm_reg_field::type_id::create("PclkDCDSettleAC",,get_full_name());
      this.PclkDCDSettleAC.configure(this, 7, 4, "RW", 0, 7'h4, 1, 0, 0);
      this.PclkDCDSampTimeAC = uvm_reg_field::type_id::create("PclkDCDSampTimeAC",,get_full_name());
      this.PclkDCDSampTimeAC.configure(this, 4, 11, "RW", 0, 4'h2, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_PclkDCAStaticCtrl0AC_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_PclkDCAStaticCtrl0AC_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r8_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDly_r8_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly_r8_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDly_r8_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly_r8_p3 = uvm_reg_field::type_id::create("ACXTxDly_r8_p3",,get_full_name());
      this.ACXTxDly_r8_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r8_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r8_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r8_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDly2nMode_r8_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly2nMode_r8_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r8_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly2nMode_r8_p3 = uvm_reg_field::type_id::create("ACXTxDly2nMode_r8_p3",,get_full_name());
      this.ACXTxDly2nMode_r8_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r8_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r8_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r9_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDly_r9_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly_r9_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDly_r9_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly_r9_p3 = uvm_reg_field::type_id::create("ACXTxDly_r9_p3",,get_full_name());
      this.ACXTxDly_r9_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r9_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r9_p3


class ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r9_p3 extends uvm_reg;
	rand uvm_reg_field ACXTxDly2nMode_r9_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly2nMode_r9_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r9_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly2nMode_r9_p3 = uvm_reg_field::type_id::create("ACXTxDly2nMode_r9_p3",,get_full_name());
      this.ACXTxDly2nMode_r9_p3.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r9_p3)

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
endclass : ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r9_p3


class ral_block_DWC_DDRPHYA_AC0_p3 extends uvm_reg_block;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_AcPipeEn_p3 AcPipeEn_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_CkVal_p3 CkVal_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_CkDisVal_p3 CkDisVal_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACSingleEndedMode_p3 ACSingleEndedMode_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_RxAcVrefControl_p3 RxAcVrefControl_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ATxDlySelect_p3 ATxDlySelect_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r0_p3 ACXTxDly_r0_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_CKXTxDly_p3 CKXTxDly_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDlyDTO_p3 ACXTxDlyDTO_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r0_p3 ACXTxDly2nMode_r0_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_AcLcdlUpdInterval_p3 AcLcdlUpdInterval_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_LcdlCalSeqUpdCK_p3 LcdlCalSeqUpdCK_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_PUBReservedP1_p3 PUBReservedP1_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_PclkDCDCtrl_p3 PclkDCDCtrl_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r1_p3 ACXTxDly_r1_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r1_p3 ACXTxDly2nMode_r1_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r2_p3 ACXTxDly_r2_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r2_p3 ACXTxDly2nMode_r2_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r3_p3 ACXTxDly_r3_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r3_p3 ACXTxDly2nMode_r3_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r4_p3 ACXTxDly_r4_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r4_p3 ACXTxDly2nMode_r4_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r5_p3 ACXTxDly_r5_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r5_p3 ACXTxDly2nMode_r5_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r6_p3 ACXTxDly_r6_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r6_p3 ACXTxDly2nMode_r6_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r7_p3 ACXTxDly_r7_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r7_p3 ACXTxDly2nMode_r7_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_PclkDCAStaticCtrl0AC_p3 PclkDCAStaticCtrl0AC_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r8_p3 ACXTxDly_r8_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r8_p3 ACXTxDly2nMode_r8_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r9_p3 ACXTxDly_r9_p3;
	rand ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r9_p3 ACXTxDly2nMode_r9_p3;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field AcPipeEn_p3_AcPipeEn_p3;
	rand uvm_reg_field CkVal_p3_CkVal_p3;
	uvm_reg_field CkDisVal_p3_Reserved;
	uvm_reg_field Reserved;
	rand uvm_reg_field CkDisVal_p3_CkDisVal_p3;
	rand uvm_reg_field ACSingleEndedMode_p3_SingleEndedCK;
	rand uvm_reg_field SingleEndedCK;
	rand uvm_reg_field RxAcVrefControl_p3_RxAcVrefDac;
	rand uvm_reg_field RxAcVrefDac;
	rand uvm_reg_field RxAcVrefControl_p3_RxAcVrefDacEn;
	rand uvm_reg_field RxAcVrefDacEn;
	rand uvm_reg_field ATxDlySelect_p3_ATxDlySelect_p3;
	rand uvm_reg_field ACXTxDly_r0_p3_ACXTxDly_r0_p3;
	rand uvm_reg_field CKXTxDly_p3_CKXTxDly_p3;
	rand uvm_reg_field ACXTxDlyDTO_p3_ACXTxDlyDTO_p3;
	rand uvm_reg_field ACXTxDly2nMode_r0_p3_ACXTxDly2nMode_r0_p3;
	rand uvm_reg_field AcLcdlUpdInterval_p3_AcLcdlUpdInterval_p3;
	rand uvm_reg_field LcdlCalSeqUpdCK_p3_LcdlCalSeqUpdCK_p3;
	rand uvm_reg_field PUBReservedP1_p3_PUBReservedP1_p3;
	rand uvm_reg_field PclkDCDCtrl_p3_PclkDCDEn;
	rand uvm_reg_field PclkDCDEn;
	rand uvm_reg_field PclkDCDCtrl_p3_PclkDCDOffsetMode;
	rand uvm_reg_field PclkDCDOffsetMode;
	rand uvm_reg_field ACXTxDly_r1_p3_ACXTxDly_r1_p3;
	rand uvm_reg_field ACXTxDly2nMode_r1_p3_ACXTxDly2nMode_r1_p3;
	rand uvm_reg_field ACXTxDly_r2_p3_ACXTxDly_r2_p3;
	rand uvm_reg_field ACXTxDly2nMode_r2_p3_ACXTxDly2nMode_r2_p3;
	rand uvm_reg_field ACXTxDly_r3_p3_ACXTxDly_r3_p3;
	rand uvm_reg_field ACXTxDly2nMode_r3_p3_ACXTxDly2nMode_r3_p3;
	rand uvm_reg_field ACXTxDly_r4_p3_ACXTxDly_r4_p3;
	rand uvm_reg_field ACXTxDly2nMode_r4_p3_ACXTxDly2nMode_r4_p3;
	rand uvm_reg_field ACXTxDly_r5_p3_ACXTxDly_r5_p3;
	rand uvm_reg_field ACXTxDly2nMode_r5_p3_ACXTxDly2nMode_r5_p3;
	rand uvm_reg_field ACXTxDly_r6_p3_ACXTxDly_r6_p3;
	rand uvm_reg_field ACXTxDly2nMode_r6_p3_ACXTxDly2nMode_r6_p3;
	rand uvm_reg_field ACXTxDly_r7_p3_ACXTxDly_r7_p3;
	rand uvm_reg_field ACXTxDly2nMode_r7_p3_ACXTxDly2nMode_r7_p3;
	rand uvm_reg_field PclkDCAStaticCtrl0AC_p3_PclkDCACalModeAC;
	rand uvm_reg_field PclkDCACalModeAC;
	rand uvm_reg_field PclkDCAStaticCtrl0AC_p3_PclkDCAEnAC;
	rand uvm_reg_field PclkDCAEnAC;
	rand uvm_reg_field PclkDCAStaticCtrl0AC_p3_PclkDCATxLcdlPhSelAC;
	rand uvm_reg_field PclkDCATxLcdlPhSelAC;
	rand uvm_reg_field PclkDCAStaticCtrl0AC_p3_PclkDCDSettleAC;
	rand uvm_reg_field PclkDCDSettleAC;
	rand uvm_reg_field PclkDCAStaticCtrl0AC_p3_PclkDCDSampTimeAC;
	rand uvm_reg_field PclkDCDSampTimeAC;
	rand uvm_reg_field ACXTxDly_r8_p3_ACXTxDly_r8_p3;
	rand uvm_reg_field ACXTxDly2nMode_r8_p3_ACXTxDly2nMode_r8_p3;
	rand uvm_reg_field ACXTxDly_r9_p3_ACXTxDly_r9_p3;
	rand uvm_reg_field ACXTxDly2nMode_r9_p3_ACXTxDly2nMode_r9_p3;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	AcPipeEn_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h8 };
		option.weight = 1;
	}

	CkVal_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hE };
		option.weight = 1;
	}

	CkDisVal_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF };
		option.weight = 1;
	}

	ACSingleEndedMode_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h15 };
		option.weight = 1;
	}

	RxAcVrefControl_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h25 };
		option.weight = 1;
	}

	ATxDlySelect_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h8F };
		option.weight = 1;
	}

	ACXTxDly_r0_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD8 };
		option.weight = 1;
	}

	CKXTxDly_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD9 };
		option.weight = 1;
	}

	ACXTxDlyDTO_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hDA };
		option.weight = 1;
	}

	ACXTxDly2nMode_r0_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hDE };
		option.weight = 1;
	}

	AcLcdlUpdInterval_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hEB };
		option.weight = 1;
	}

	LcdlCalSeqUpdCK_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hEC };
		option.weight = 1;
	}

	PUBReservedP1_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFF };
		option.weight = 1;
	}

	PclkDCDCtrl_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h100 };
		option.weight = 1;
	}

	ACXTxDly_r1_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1D8 };
		option.weight = 1;
	}

	ACXTxDly2nMode_r1_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1DE };
		option.weight = 1;
	}

	ACXTxDly_r2_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2D8 };
		option.weight = 1;
	}

	ACXTxDly2nMode_r2_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2DE };
		option.weight = 1;
	}

	ACXTxDly_r3_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3D8 };
		option.weight = 1;
	}

	ACXTxDly2nMode_r3_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3DE };
		option.weight = 1;
	}

	ACXTxDly_r4_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4D8 };
		option.weight = 1;
	}

	ACXTxDly2nMode_r4_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4DE };
		option.weight = 1;
	}

	ACXTxDly_r5_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5D8 };
		option.weight = 1;
	}

	ACXTxDly2nMode_r5_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5DE };
		option.weight = 1;
	}

	ACXTxDly_r6_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h6D8 };
		option.weight = 1;
	}

	ACXTxDly2nMode_r6_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h6DE };
		option.weight = 1;
	}

	ACXTxDly_r7_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h7D8 };
		option.weight = 1;
	}

	ACXTxDly2nMode_r7_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h7DE };
		option.weight = 1;
	}

	PclkDCAStaticCtrl0AC_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h803 };
		option.weight = 1;
	}

	ACXTxDly_r8_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h8D8 };
		option.weight = 1;
	}

	ACXTxDly2nMode_r8_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h8DE };
		option.weight = 1;
	}

	ACXTxDly_r9_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h9D8 };
		option.weight = 1;
	}

	ACXTxDly2nMode_r9_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h9DE };
		option.weight = 1;
	}
endgroup
	function new(string name = "DWC_DDRPHYA_AC0_p3");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.AcPipeEn_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_AcPipeEn_p3::type_id::create("AcPipeEn_p3",,get_full_name());
      if(this.AcPipeEn_p3.has_coverage(UVM_CVR_ALL))
      	this.AcPipeEn_p3.cg_bits.option.name = {get_name(), ".", "AcPipeEn_p3_bits"};
      this.AcPipeEn_p3.configure(this, null, "");
      this.AcPipeEn_p3.build();
      this.default_map.add_reg(this.AcPipeEn_p3, `UVM_REG_ADDR_WIDTH'h8, "RW", 0);
		this.AcPipeEn_p3_AcPipeEn_p3 = this.AcPipeEn_p3.AcPipeEn_p3;
      this.CkVal_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_CkVal_p3::type_id::create("CkVal_p3",,get_full_name());
      if(this.CkVal_p3.has_coverage(UVM_CVR_ALL))
      	this.CkVal_p3.cg_bits.option.name = {get_name(), ".", "CkVal_p3_bits"};
      this.CkVal_p3.configure(this, null, "");
      this.CkVal_p3.build();
      this.default_map.add_reg(this.CkVal_p3, `UVM_REG_ADDR_WIDTH'hE, "RW", 0);
		this.CkVal_p3_CkVal_p3 = this.CkVal_p3.CkVal_p3;
      this.CkDisVal_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_CkDisVal_p3::type_id::create("CkDisVal_p3",,get_full_name());
      if(this.CkDisVal_p3.has_coverage(UVM_CVR_ALL))
      	this.CkDisVal_p3.cg_bits.option.name = {get_name(), ".", "CkDisVal_p3_bits"};
      this.CkDisVal_p3.configure(this, null, "");
      this.CkDisVal_p3.build();
      this.default_map.add_reg(this.CkDisVal_p3, `UVM_REG_ADDR_WIDTH'hF, "RW", 0);
		this.CkDisVal_p3_Reserved = this.CkDisVal_p3.Reserved;
		this.Reserved = this.CkDisVal_p3.Reserved;
		this.CkDisVal_p3_CkDisVal_p3 = this.CkDisVal_p3.CkDisVal_p3;
      this.ACSingleEndedMode_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACSingleEndedMode_p3::type_id::create("ACSingleEndedMode_p3",,get_full_name());
      if(this.ACSingleEndedMode_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSingleEndedMode_p3.cg_bits.option.name = {get_name(), ".", "ACSingleEndedMode_p3_bits"};
      this.ACSingleEndedMode_p3.configure(this, null, "");
      this.ACSingleEndedMode_p3.build();
      this.default_map.add_reg(this.ACSingleEndedMode_p3, `UVM_REG_ADDR_WIDTH'h15, "RW", 0);
		this.ACSingleEndedMode_p3_SingleEndedCK = this.ACSingleEndedMode_p3.SingleEndedCK;
		this.SingleEndedCK = this.ACSingleEndedMode_p3.SingleEndedCK;
      this.RxAcVrefControl_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_RxAcVrefControl_p3::type_id::create("RxAcVrefControl_p3",,get_full_name());
      if(this.RxAcVrefControl_p3.has_coverage(UVM_CVR_ALL))
      	this.RxAcVrefControl_p3.cg_bits.option.name = {get_name(), ".", "RxAcVrefControl_p3_bits"};
      this.RxAcVrefControl_p3.configure(this, null, "");
      this.RxAcVrefControl_p3.build();
      this.default_map.add_reg(this.RxAcVrefControl_p3, `UVM_REG_ADDR_WIDTH'h25, "RW", 0);
		this.RxAcVrefControl_p3_RxAcVrefDac = this.RxAcVrefControl_p3.RxAcVrefDac;
		this.RxAcVrefDac = this.RxAcVrefControl_p3.RxAcVrefDac;
		this.RxAcVrefControl_p3_RxAcVrefDacEn = this.RxAcVrefControl_p3.RxAcVrefDacEn;
		this.RxAcVrefDacEn = this.RxAcVrefControl_p3.RxAcVrefDacEn;
      this.ATxDlySelect_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ATxDlySelect_p3::type_id::create("ATxDlySelect_p3",,get_full_name());
      if(this.ATxDlySelect_p3.has_coverage(UVM_CVR_ALL))
      	this.ATxDlySelect_p3.cg_bits.option.name = {get_name(), ".", "ATxDlySelect_p3_bits"};
      this.ATxDlySelect_p3.configure(this, null, "");
      this.ATxDlySelect_p3.build();
      this.default_map.add_reg(this.ATxDlySelect_p3, `UVM_REG_ADDR_WIDTH'h8F, "RW", 0);
		this.ATxDlySelect_p3_ATxDlySelect_p3 = this.ATxDlySelect_p3.ATxDlySelect_p3;
      this.ACXTxDly_r0_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r0_p3::type_id::create("ACXTxDly_r0_p3",,get_full_name());
      if(this.ACXTxDly_r0_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly_r0_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDly_r0_p3_bits"};
      this.ACXTxDly_r0_p3.configure(this, null, "");
      this.ACXTxDly_r0_p3.build();
      this.default_map.add_reg(this.ACXTxDly_r0_p3, `UVM_REG_ADDR_WIDTH'hD8, "RW", 0);
		this.ACXTxDly_r0_p3_ACXTxDly_r0_p3 = this.ACXTxDly_r0_p3.ACXTxDly_r0_p3;
      this.CKXTxDly_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_CKXTxDly_p3::type_id::create("CKXTxDly_p3",,get_full_name());
      if(this.CKXTxDly_p3.has_coverage(UVM_CVR_ALL))
      	this.CKXTxDly_p3.cg_bits.option.name = {get_name(), ".", "CKXTxDly_p3_bits"};
      this.CKXTxDly_p3.configure(this, null, "");
      this.CKXTxDly_p3.build();
      this.default_map.add_reg(this.CKXTxDly_p3, `UVM_REG_ADDR_WIDTH'hD9, "RW", 0);
		this.CKXTxDly_p3_CKXTxDly_p3 = this.CKXTxDly_p3.CKXTxDly_p3;
      this.ACXTxDlyDTO_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDlyDTO_p3::type_id::create("ACXTxDlyDTO_p3",,get_full_name());
      if(this.ACXTxDlyDTO_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDlyDTO_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDlyDTO_p3_bits"};
      this.ACXTxDlyDTO_p3.configure(this, null, "");
      this.ACXTxDlyDTO_p3.build();
      this.default_map.add_reg(this.ACXTxDlyDTO_p3, `UVM_REG_ADDR_WIDTH'hDA, "RW", 0);
		this.ACXTxDlyDTO_p3_ACXTxDlyDTO_p3 = this.ACXTxDlyDTO_p3.ACXTxDlyDTO_p3;
      this.ACXTxDly2nMode_r0_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r0_p3::type_id::create("ACXTxDly2nMode_r0_p3",,get_full_name());
      if(this.ACXTxDly2nMode_r0_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly2nMode_r0_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDly2nMode_r0_p3_bits"};
      this.ACXTxDly2nMode_r0_p3.configure(this, null, "");
      this.ACXTxDly2nMode_r0_p3.build();
      this.default_map.add_reg(this.ACXTxDly2nMode_r0_p3, `UVM_REG_ADDR_WIDTH'hDE, "RW", 0);
		this.ACXTxDly2nMode_r0_p3_ACXTxDly2nMode_r0_p3 = this.ACXTxDly2nMode_r0_p3.ACXTxDly2nMode_r0_p3;
      this.AcLcdlUpdInterval_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_AcLcdlUpdInterval_p3::type_id::create("AcLcdlUpdInterval_p3",,get_full_name());
      if(this.AcLcdlUpdInterval_p3.has_coverage(UVM_CVR_ALL))
      	this.AcLcdlUpdInterval_p3.cg_bits.option.name = {get_name(), ".", "AcLcdlUpdInterval_p3_bits"};
      this.AcLcdlUpdInterval_p3.configure(this, null, "");
      this.AcLcdlUpdInterval_p3.build();
      this.default_map.add_reg(this.AcLcdlUpdInterval_p3, `UVM_REG_ADDR_WIDTH'hEB, "RW", 0);
		this.AcLcdlUpdInterval_p3_AcLcdlUpdInterval_p3 = this.AcLcdlUpdInterval_p3.AcLcdlUpdInterval_p3;
      this.LcdlCalSeqUpdCK_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_LcdlCalSeqUpdCK_p3::type_id::create("LcdlCalSeqUpdCK_p3",,get_full_name());
      if(this.LcdlCalSeqUpdCK_p3.has_coverage(UVM_CVR_ALL))
      	this.LcdlCalSeqUpdCK_p3.cg_bits.option.name = {get_name(), ".", "LcdlCalSeqUpdCK_p3_bits"};
      this.LcdlCalSeqUpdCK_p3.configure(this, null, "");
      this.LcdlCalSeqUpdCK_p3.build();
      this.default_map.add_reg(this.LcdlCalSeqUpdCK_p3, `UVM_REG_ADDR_WIDTH'hEC, "RW", 0);
		this.LcdlCalSeqUpdCK_p3_LcdlCalSeqUpdCK_p3 = this.LcdlCalSeqUpdCK_p3.LcdlCalSeqUpdCK_p3;
      this.PUBReservedP1_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_PUBReservedP1_p3::type_id::create("PUBReservedP1_p3",,get_full_name());
      if(this.PUBReservedP1_p3.has_coverage(UVM_CVR_ALL))
      	this.PUBReservedP1_p3.cg_bits.option.name = {get_name(), ".", "PUBReservedP1_p3_bits"};
      this.PUBReservedP1_p3.configure(this, null, "");
      this.PUBReservedP1_p3.build();
      this.default_map.add_reg(this.PUBReservedP1_p3, `UVM_REG_ADDR_WIDTH'hFF, "RW", 0);
		this.PUBReservedP1_p3_PUBReservedP1_p3 = this.PUBReservedP1_p3.PUBReservedP1_p3;
      this.PclkDCDCtrl_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_PclkDCDCtrl_p3::type_id::create("PclkDCDCtrl_p3",,get_full_name());
      if(this.PclkDCDCtrl_p3.has_coverage(UVM_CVR_ALL))
      	this.PclkDCDCtrl_p3.cg_bits.option.name = {get_name(), ".", "PclkDCDCtrl_p3_bits"};
      this.PclkDCDCtrl_p3.configure(this, null, "");
      this.PclkDCDCtrl_p3.build();
      this.default_map.add_reg(this.PclkDCDCtrl_p3, `UVM_REG_ADDR_WIDTH'h100, "RW", 0);
		this.PclkDCDCtrl_p3_PclkDCDEn = this.PclkDCDCtrl_p3.PclkDCDEn;
		this.PclkDCDEn = this.PclkDCDCtrl_p3.PclkDCDEn;
		this.PclkDCDCtrl_p3_PclkDCDOffsetMode = this.PclkDCDCtrl_p3.PclkDCDOffsetMode;
		this.PclkDCDOffsetMode = this.PclkDCDCtrl_p3.PclkDCDOffsetMode;
      this.ACXTxDly_r1_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r1_p3::type_id::create("ACXTxDly_r1_p3",,get_full_name());
      if(this.ACXTxDly_r1_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly_r1_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDly_r1_p3_bits"};
      this.ACXTxDly_r1_p3.configure(this, null, "");
      this.ACXTxDly_r1_p3.build();
      this.default_map.add_reg(this.ACXTxDly_r1_p3, `UVM_REG_ADDR_WIDTH'h1D8, "RW", 0);
		this.ACXTxDly_r1_p3_ACXTxDly_r1_p3 = this.ACXTxDly_r1_p3.ACXTxDly_r1_p3;
      this.ACXTxDly2nMode_r1_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r1_p3::type_id::create("ACXTxDly2nMode_r1_p3",,get_full_name());
      if(this.ACXTxDly2nMode_r1_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly2nMode_r1_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDly2nMode_r1_p3_bits"};
      this.ACXTxDly2nMode_r1_p3.configure(this, null, "");
      this.ACXTxDly2nMode_r1_p3.build();
      this.default_map.add_reg(this.ACXTxDly2nMode_r1_p3, `UVM_REG_ADDR_WIDTH'h1DE, "RW", 0);
		this.ACXTxDly2nMode_r1_p3_ACXTxDly2nMode_r1_p3 = this.ACXTxDly2nMode_r1_p3.ACXTxDly2nMode_r1_p3;
      this.ACXTxDly_r2_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r2_p3::type_id::create("ACXTxDly_r2_p3",,get_full_name());
      if(this.ACXTxDly_r2_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly_r2_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDly_r2_p3_bits"};
      this.ACXTxDly_r2_p3.configure(this, null, "");
      this.ACXTxDly_r2_p3.build();
      this.default_map.add_reg(this.ACXTxDly_r2_p3, `UVM_REG_ADDR_WIDTH'h2D8, "RW", 0);
		this.ACXTxDly_r2_p3_ACXTxDly_r2_p3 = this.ACXTxDly_r2_p3.ACXTxDly_r2_p3;
      this.ACXTxDly2nMode_r2_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r2_p3::type_id::create("ACXTxDly2nMode_r2_p3",,get_full_name());
      if(this.ACXTxDly2nMode_r2_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly2nMode_r2_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDly2nMode_r2_p3_bits"};
      this.ACXTxDly2nMode_r2_p3.configure(this, null, "");
      this.ACXTxDly2nMode_r2_p3.build();
      this.default_map.add_reg(this.ACXTxDly2nMode_r2_p3, `UVM_REG_ADDR_WIDTH'h2DE, "RW", 0);
		this.ACXTxDly2nMode_r2_p3_ACXTxDly2nMode_r2_p3 = this.ACXTxDly2nMode_r2_p3.ACXTxDly2nMode_r2_p3;
      this.ACXTxDly_r3_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r3_p3::type_id::create("ACXTxDly_r3_p3",,get_full_name());
      if(this.ACXTxDly_r3_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly_r3_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDly_r3_p3_bits"};
      this.ACXTxDly_r3_p3.configure(this, null, "");
      this.ACXTxDly_r3_p3.build();
      this.default_map.add_reg(this.ACXTxDly_r3_p3, `UVM_REG_ADDR_WIDTH'h3D8, "RW", 0);
		this.ACXTxDly_r3_p3_ACXTxDly_r3_p3 = this.ACXTxDly_r3_p3.ACXTxDly_r3_p3;
      this.ACXTxDly2nMode_r3_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r3_p3::type_id::create("ACXTxDly2nMode_r3_p3",,get_full_name());
      if(this.ACXTxDly2nMode_r3_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly2nMode_r3_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDly2nMode_r3_p3_bits"};
      this.ACXTxDly2nMode_r3_p3.configure(this, null, "");
      this.ACXTxDly2nMode_r3_p3.build();
      this.default_map.add_reg(this.ACXTxDly2nMode_r3_p3, `UVM_REG_ADDR_WIDTH'h3DE, "RW", 0);
		this.ACXTxDly2nMode_r3_p3_ACXTxDly2nMode_r3_p3 = this.ACXTxDly2nMode_r3_p3.ACXTxDly2nMode_r3_p3;
      this.ACXTxDly_r4_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r4_p3::type_id::create("ACXTxDly_r4_p3",,get_full_name());
      if(this.ACXTxDly_r4_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly_r4_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDly_r4_p3_bits"};
      this.ACXTxDly_r4_p3.configure(this, null, "");
      this.ACXTxDly_r4_p3.build();
      this.default_map.add_reg(this.ACXTxDly_r4_p3, `UVM_REG_ADDR_WIDTH'h4D8, "RW", 0);
		this.ACXTxDly_r4_p3_ACXTxDly_r4_p3 = this.ACXTxDly_r4_p3.ACXTxDly_r4_p3;
      this.ACXTxDly2nMode_r4_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r4_p3::type_id::create("ACXTxDly2nMode_r4_p3",,get_full_name());
      if(this.ACXTxDly2nMode_r4_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly2nMode_r4_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDly2nMode_r4_p3_bits"};
      this.ACXTxDly2nMode_r4_p3.configure(this, null, "");
      this.ACXTxDly2nMode_r4_p3.build();
      this.default_map.add_reg(this.ACXTxDly2nMode_r4_p3, `UVM_REG_ADDR_WIDTH'h4DE, "RW", 0);
		this.ACXTxDly2nMode_r4_p3_ACXTxDly2nMode_r4_p3 = this.ACXTxDly2nMode_r4_p3.ACXTxDly2nMode_r4_p3;
      this.ACXTxDly_r5_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r5_p3::type_id::create("ACXTxDly_r5_p3",,get_full_name());
      if(this.ACXTxDly_r5_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly_r5_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDly_r5_p3_bits"};
      this.ACXTxDly_r5_p3.configure(this, null, "");
      this.ACXTxDly_r5_p3.build();
      this.default_map.add_reg(this.ACXTxDly_r5_p3, `UVM_REG_ADDR_WIDTH'h5D8, "RW", 0);
		this.ACXTxDly_r5_p3_ACXTxDly_r5_p3 = this.ACXTxDly_r5_p3.ACXTxDly_r5_p3;
      this.ACXTxDly2nMode_r5_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r5_p3::type_id::create("ACXTxDly2nMode_r5_p3",,get_full_name());
      if(this.ACXTxDly2nMode_r5_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly2nMode_r5_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDly2nMode_r5_p3_bits"};
      this.ACXTxDly2nMode_r5_p3.configure(this, null, "");
      this.ACXTxDly2nMode_r5_p3.build();
      this.default_map.add_reg(this.ACXTxDly2nMode_r5_p3, `UVM_REG_ADDR_WIDTH'h5DE, "RW", 0);
		this.ACXTxDly2nMode_r5_p3_ACXTxDly2nMode_r5_p3 = this.ACXTxDly2nMode_r5_p3.ACXTxDly2nMode_r5_p3;
      this.ACXTxDly_r6_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r6_p3::type_id::create("ACXTxDly_r6_p3",,get_full_name());
      if(this.ACXTxDly_r6_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly_r6_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDly_r6_p3_bits"};
      this.ACXTxDly_r6_p3.configure(this, null, "");
      this.ACXTxDly_r6_p3.build();
      this.default_map.add_reg(this.ACXTxDly_r6_p3, `UVM_REG_ADDR_WIDTH'h6D8, "RW", 0);
		this.ACXTxDly_r6_p3_ACXTxDly_r6_p3 = this.ACXTxDly_r6_p3.ACXTxDly_r6_p3;
      this.ACXTxDly2nMode_r6_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r6_p3::type_id::create("ACXTxDly2nMode_r6_p3",,get_full_name());
      if(this.ACXTxDly2nMode_r6_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly2nMode_r6_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDly2nMode_r6_p3_bits"};
      this.ACXTxDly2nMode_r6_p3.configure(this, null, "");
      this.ACXTxDly2nMode_r6_p3.build();
      this.default_map.add_reg(this.ACXTxDly2nMode_r6_p3, `UVM_REG_ADDR_WIDTH'h6DE, "RW", 0);
		this.ACXTxDly2nMode_r6_p3_ACXTxDly2nMode_r6_p3 = this.ACXTxDly2nMode_r6_p3.ACXTxDly2nMode_r6_p3;
      this.ACXTxDly_r7_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r7_p3::type_id::create("ACXTxDly_r7_p3",,get_full_name());
      if(this.ACXTxDly_r7_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly_r7_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDly_r7_p3_bits"};
      this.ACXTxDly_r7_p3.configure(this, null, "");
      this.ACXTxDly_r7_p3.build();
      this.default_map.add_reg(this.ACXTxDly_r7_p3, `UVM_REG_ADDR_WIDTH'h7D8, "RW", 0);
		this.ACXTxDly_r7_p3_ACXTxDly_r7_p3 = this.ACXTxDly_r7_p3.ACXTxDly_r7_p3;
      this.ACXTxDly2nMode_r7_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r7_p3::type_id::create("ACXTxDly2nMode_r7_p3",,get_full_name());
      if(this.ACXTxDly2nMode_r7_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly2nMode_r7_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDly2nMode_r7_p3_bits"};
      this.ACXTxDly2nMode_r7_p3.configure(this, null, "");
      this.ACXTxDly2nMode_r7_p3.build();
      this.default_map.add_reg(this.ACXTxDly2nMode_r7_p3, `UVM_REG_ADDR_WIDTH'h7DE, "RW", 0);
		this.ACXTxDly2nMode_r7_p3_ACXTxDly2nMode_r7_p3 = this.ACXTxDly2nMode_r7_p3.ACXTxDly2nMode_r7_p3;
      this.PclkDCAStaticCtrl0AC_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_PclkDCAStaticCtrl0AC_p3::type_id::create("PclkDCAStaticCtrl0AC_p3",,get_full_name());
      if(this.PclkDCAStaticCtrl0AC_p3.has_coverage(UVM_CVR_ALL))
      	this.PclkDCAStaticCtrl0AC_p3.cg_bits.option.name = {get_name(), ".", "PclkDCAStaticCtrl0AC_p3_bits"};
      this.PclkDCAStaticCtrl0AC_p3.configure(this, null, "");
      this.PclkDCAStaticCtrl0AC_p3.build();
      this.default_map.add_reg(this.PclkDCAStaticCtrl0AC_p3, `UVM_REG_ADDR_WIDTH'h803, "RW", 0);
		this.PclkDCAStaticCtrl0AC_p3_PclkDCACalModeAC = this.PclkDCAStaticCtrl0AC_p3.PclkDCACalModeAC;
		this.PclkDCACalModeAC = this.PclkDCAStaticCtrl0AC_p3.PclkDCACalModeAC;
		this.PclkDCAStaticCtrl0AC_p3_PclkDCAEnAC = this.PclkDCAStaticCtrl0AC_p3.PclkDCAEnAC;
		this.PclkDCAEnAC = this.PclkDCAStaticCtrl0AC_p3.PclkDCAEnAC;
		this.PclkDCAStaticCtrl0AC_p3_PclkDCATxLcdlPhSelAC = this.PclkDCAStaticCtrl0AC_p3.PclkDCATxLcdlPhSelAC;
		this.PclkDCATxLcdlPhSelAC = this.PclkDCAStaticCtrl0AC_p3.PclkDCATxLcdlPhSelAC;
		this.PclkDCAStaticCtrl0AC_p3_PclkDCDSettleAC = this.PclkDCAStaticCtrl0AC_p3.PclkDCDSettleAC;
		this.PclkDCDSettleAC = this.PclkDCAStaticCtrl0AC_p3.PclkDCDSettleAC;
		this.PclkDCAStaticCtrl0AC_p3_PclkDCDSampTimeAC = this.PclkDCAStaticCtrl0AC_p3.PclkDCDSampTimeAC;
		this.PclkDCDSampTimeAC = this.PclkDCAStaticCtrl0AC_p3.PclkDCDSampTimeAC;
      this.ACXTxDly_r8_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r8_p3::type_id::create("ACXTxDly_r8_p3",,get_full_name());
      if(this.ACXTxDly_r8_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly_r8_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDly_r8_p3_bits"};
      this.ACXTxDly_r8_p3.configure(this, null, "");
      this.ACXTxDly_r8_p3.build();
      this.default_map.add_reg(this.ACXTxDly_r8_p3, `UVM_REG_ADDR_WIDTH'h8D8, "RW", 0);
		this.ACXTxDly_r8_p3_ACXTxDly_r8_p3 = this.ACXTxDly_r8_p3.ACXTxDly_r8_p3;
      this.ACXTxDly2nMode_r8_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r8_p3::type_id::create("ACXTxDly2nMode_r8_p3",,get_full_name());
      if(this.ACXTxDly2nMode_r8_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly2nMode_r8_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDly2nMode_r8_p3_bits"};
      this.ACXTxDly2nMode_r8_p3.configure(this, null, "");
      this.ACXTxDly2nMode_r8_p3.build();
      this.default_map.add_reg(this.ACXTxDly2nMode_r8_p3, `UVM_REG_ADDR_WIDTH'h8DE, "RW", 0);
		this.ACXTxDly2nMode_r8_p3_ACXTxDly2nMode_r8_p3 = this.ACXTxDly2nMode_r8_p3.ACXTxDly2nMode_r8_p3;
      this.ACXTxDly_r9_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly_r9_p3::type_id::create("ACXTxDly_r9_p3",,get_full_name());
      if(this.ACXTxDly_r9_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly_r9_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDly_r9_p3_bits"};
      this.ACXTxDly_r9_p3.configure(this, null, "");
      this.ACXTxDly_r9_p3.build();
      this.default_map.add_reg(this.ACXTxDly_r9_p3, `UVM_REG_ADDR_WIDTH'h9D8, "RW", 0);
		this.ACXTxDly_r9_p3_ACXTxDly_r9_p3 = this.ACXTxDly_r9_p3.ACXTxDly_r9_p3;
      this.ACXTxDly2nMode_r9_p3 = ral_reg_DWC_DDRPHYA_AC0_p3_ACXTxDly2nMode_r9_p3::type_id::create("ACXTxDly2nMode_r9_p3",,get_full_name());
      if(this.ACXTxDly2nMode_r9_p3.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly2nMode_r9_p3.cg_bits.option.name = {get_name(), ".", "ACXTxDly2nMode_r9_p3_bits"};
      this.ACXTxDly2nMode_r9_p3.configure(this, null, "");
      this.ACXTxDly2nMode_r9_p3.build();
      this.default_map.add_reg(this.ACXTxDly2nMode_r9_p3, `UVM_REG_ADDR_WIDTH'h9DE, "RW", 0);
		this.ACXTxDly2nMode_r9_p3_ACXTxDly2nMode_r9_p3 = this.ACXTxDly2nMode_r9_p3.ACXTxDly2nMode_r9_p3;
   endfunction : build

	`uvm_object_utils(ral_block_DWC_DDRPHYA_AC0_p3)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_DDRPHYA_AC0_p3


endpackage
`endif
