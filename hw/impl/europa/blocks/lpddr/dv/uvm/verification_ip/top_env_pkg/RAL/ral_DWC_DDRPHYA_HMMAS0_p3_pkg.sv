`ifndef RAL_DWC_DDRPHYA_HMMAS0_P3_PKG
`define RAL_DWC_DDRPHYA_HMMAS0_P3_PKG

package ral_DWC_DDRPHYA_HMMAS0_p3_pkg;
import uvm_pkg::*;

class ral_reg_DWC_DDRPHYA_HMMAS0_p3_CPllCtrl1_p3 extends uvm_reg;
	rand uvm_reg_field CPllCpIntCtrl;
	rand uvm_reg_field CReservedPllCpIntCtrl;
	rand uvm_reg_field CPllCpPropCtrl;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllCpIntCtrl: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   CReservedPllCpIntCtrl: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CPllCpPropCtrl: coverpoint {m_data[14:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p3_CPllCtrl1_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllCpIntCtrl = uvm_reg_field::type_id::create("CPllCpIntCtrl",,get_full_name());
      this.CPllCpIntCtrl.configure(this, 7, 0, "RW", 0, 7'h18, 1, 0, 0);
      this.CReservedPllCpIntCtrl = uvm_reg_field::type_id::create("CReservedPllCpIntCtrl",,get_full_name());
      this.CReservedPllCpIntCtrl.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.CPllCpPropCtrl = uvm_reg_field::type_id::create("CPllCpPropCtrl",,get_full_name());
      this.CPllCpPropCtrl.configure(this, 7, 8, "RW", 0, 7'h2c, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p3_CPllCtrl1_p3)

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
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p3_CPllCtrl1_p3


class ral_reg_DWC_DDRPHYA_HMMAS0_p3_CPllCtrl4_p3 extends uvm_reg;
	rand uvm_reg_field CPllCpIntGsCtrl;
	rand uvm_reg_field CReservedPllCpIntGsCtrl;
	rand uvm_reg_field CPllCpPropGsCtrl;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllCpIntGsCtrl: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   CReservedPllCpIntGsCtrl: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CPllCpPropGsCtrl: coverpoint {m_data[14:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p3_CPllCtrl4_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllCpIntGsCtrl = uvm_reg_field::type_id::create("CPllCpIntGsCtrl",,get_full_name());
      this.CPllCpIntGsCtrl.configure(this, 7, 0, "RW", 0, 7'h1f, 1, 0, 0);
      this.CReservedPllCpIntGsCtrl = uvm_reg_field::type_id::create("CReservedPllCpIntGsCtrl",,get_full_name());
      this.CReservedPllCpIntGsCtrl.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.CPllCpPropGsCtrl = uvm_reg_field::type_id::create("CPllCpPropGsCtrl",,get_full_name());
      this.CPllCpPropGsCtrl.configure(this, 7, 8, "RW", 0, 7'h3c, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p3_CPllCtrl4_p3)

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
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p3_CPllCtrl4_p3


class ral_reg_DWC_DDRPHYA_HMMAS0_p3_CPllCtrl5_p3 extends uvm_reg;
	rand uvm_reg_field CPllDivSel;
	rand uvm_reg_field CPllV2IMode;
	rand uvm_reg_field CPllVcoLowFreq;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllDivSel: coverpoint {m_data[9:0], m_is_read} iff(m_be) {
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
	   CPllV2IMode: coverpoint {m_data[12:10], m_is_read} iff(m_be) {
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
	   CPllVcoLowFreq: coverpoint {m_data[15:13], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p3_CPllCtrl5_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllDivSel = uvm_reg_field::type_id::create("CPllDivSel",,get_full_name());
      this.CPllDivSel.configure(this, 10, 0, "RW", 0, 10'h3ce, 1, 0, 0);
      this.CPllV2IMode = uvm_reg_field::type_id::create("CPllV2IMode",,get_full_name());
      this.CPllV2IMode.configure(this, 3, 10, "RW", 0, 3'h2, 1, 0, 0);
      this.CPllVcoLowFreq = uvm_reg_field::type_id::create("CPllVcoLowFreq",,get_full_name());
      this.CPllVcoLowFreq.configure(this, 3, 13, "RW", 0, 3'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p3_CPllCtrl5_p3)

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
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p3_CPllCtrl5_p3


class ral_reg_DWC_DDRPHYA_HMMAS0_p3_CPllDacValIn_p3 extends uvm_reg;
	rand uvm_reg_field CPllDacValIn_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllDacValIn_p3: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p3_CPllDacValIn_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllDacValIn_p3 = uvm_reg_field::type_id::create("CPllDacValIn_p3",,get_full_name());
      this.CPllDacValIn_p3.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p3_CPllDacValIn_p3)

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
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p3_CPllDacValIn_p3


class ral_reg_DWC_DDRPHYA_HMMAS0_p3_CMasterReserved_p3 extends uvm_reg;
	rand uvm_reg_field CMasterReserved_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CMasterReserved_p3: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p3_CMasterReserved_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CMasterReserved_p3 = uvm_reg_field::type_id::create("CMasterReserved_p3",,get_full_name());
      this.CMasterReserved_p3.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p3_CMasterReserved_p3)

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
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p3_CMasterReserved_p3


class ral_reg_DWC_DDRPHYA_HMMAS0_p3_HMPclkPtrInitVal_p3 extends uvm_reg;
	rand uvm_reg_field HMPclkPtrInitVal_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HMPclkPtrInitVal_p3: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p3_HMPclkPtrInitVal_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMPclkPtrInitVal_p3 = uvm_reg_field::type_id::create("HMPclkPtrInitVal_p3",,get_full_name());
      this.HMPclkPtrInitVal_p3.configure(this, 5, 0, "RW", 0, 5'h2, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p3_HMPclkPtrInitVal_p3)

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
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p3_HMPclkPtrInitVal_p3


class ral_reg_DWC_DDRPHYA_HMMAS0_p3_HMReservedP1_p3 extends uvm_reg;
	rand uvm_reg_field HMReservedP1_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HMReservedP1_p3: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p3_HMReservedP1_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMReservedP1_p3 = uvm_reg_field::type_id::create("HMReservedP1_p3",,get_full_name());
      this.HMReservedP1_p3.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p3_HMReservedP1_p3)

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
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p3_HMReservedP1_p3


class ral_block_DWC_DDRPHYA_HMMAS0_p3 extends uvm_reg_block;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p3_CPllCtrl1_p3 CPllCtrl1_p3;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p3_CPllCtrl4_p3 CPllCtrl4_p3;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p3_CPllCtrl5_p3 CPllCtrl5_p3;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p3_CPllDacValIn_p3 CPllDacValIn_p3;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p3_CMasterReserved_p3 CMasterReserved_p3;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p3_HMPclkPtrInitVal_p3 HMPclkPtrInitVal_p3;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p3_HMReservedP1_p3 HMReservedP1_p3;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field CPllCtrl1_p3_CPllCpIntCtrl;
	rand uvm_reg_field CPllCpIntCtrl;
	rand uvm_reg_field CPllCtrl1_p3_CReservedPllCpIntCtrl;
	rand uvm_reg_field CReservedPllCpIntCtrl;
	rand uvm_reg_field CPllCtrl1_p3_CPllCpPropCtrl;
	rand uvm_reg_field CPllCpPropCtrl;
	rand uvm_reg_field CPllCtrl4_p3_CPllCpIntGsCtrl;
	rand uvm_reg_field CPllCpIntGsCtrl;
	rand uvm_reg_field CPllCtrl4_p3_CReservedPllCpIntGsCtrl;
	rand uvm_reg_field CReservedPllCpIntGsCtrl;
	rand uvm_reg_field CPllCtrl4_p3_CPllCpPropGsCtrl;
	rand uvm_reg_field CPllCpPropGsCtrl;
	rand uvm_reg_field CPllCtrl5_p3_CPllDivSel;
	rand uvm_reg_field CPllDivSel;
	rand uvm_reg_field CPllCtrl5_p3_CPllV2IMode;
	rand uvm_reg_field CPllV2IMode;
	rand uvm_reg_field CPllCtrl5_p3_CPllVcoLowFreq;
	rand uvm_reg_field CPllVcoLowFreq;
	rand uvm_reg_field CPllDacValIn_p3_CPllDacValIn_p3;
	rand uvm_reg_field CMasterReserved_p3_CMasterReserved_p3;
	rand uvm_reg_field HMPclkPtrInitVal_p3_HMPclkPtrInitVal_p3;
	rand uvm_reg_field HMReservedP1_p3_HMReservedP1_p3;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	CPllCtrl1_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5 };
		option.weight = 1;
	}

	CPllCtrl4_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h7 };
		option.weight = 1;
	}

	CPllCtrl5_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h8 };
		option.weight = 1;
	}

	CPllDacValIn_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h9 };
		option.weight = 1;
	}

	CMasterReserved_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA };
		option.weight = 1;
	}

	HMPclkPtrInitVal_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h40 };
		option.weight = 1;
	}

	HMReservedP1_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFF };
		option.weight = 1;
	}
endgroup
	function new(string name = "DWC_DDRPHYA_HMMAS0_p3");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.CPllCtrl1_p3 = ral_reg_DWC_DDRPHYA_HMMAS0_p3_CPllCtrl1_p3::type_id::create("CPllCtrl1_p3",,get_full_name());
      if(this.CPllCtrl1_p3.has_coverage(UVM_CVR_ALL))
      	this.CPllCtrl1_p3.cg_bits.option.name = {get_name(), ".", "CPllCtrl1_p3_bits"};
      this.CPllCtrl1_p3.configure(this, null, "");
      this.CPllCtrl1_p3.build();
      this.default_map.add_reg(this.CPllCtrl1_p3, `UVM_REG_ADDR_WIDTH'h5, "RW", 0);
		this.CPllCtrl1_p3_CPllCpIntCtrl = this.CPllCtrl1_p3.CPllCpIntCtrl;
		this.CPllCpIntCtrl = this.CPllCtrl1_p3.CPllCpIntCtrl;
		this.CPllCtrl1_p3_CReservedPllCpIntCtrl = this.CPllCtrl1_p3.CReservedPllCpIntCtrl;
		this.CReservedPllCpIntCtrl = this.CPllCtrl1_p3.CReservedPllCpIntCtrl;
		this.CPllCtrl1_p3_CPllCpPropCtrl = this.CPllCtrl1_p3.CPllCpPropCtrl;
		this.CPllCpPropCtrl = this.CPllCtrl1_p3.CPllCpPropCtrl;
      this.CPllCtrl4_p3 = ral_reg_DWC_DDRPHYA_HMMAS0_p3_CPllCtrl4_p3::type_id::create("CPllCtrl4_p3",,get_full_name());
      if(this.CPllCtrl4_p3.has_coverage(UVM_CVR_ALL))
      	this.CPllCtrl4_p3.cg_bits.option.name = {get_name(), ".", "CPllCtrl4_p3_bits"};
      this.CPllCtrl4_p3.configure(this, null, "");
      this.CPllCtrl4_p3.build();
      this.default_map.add_reg(this.CPllCtrl4_p3, `UVM_REG_ADDR_WIDTH'h7, "RW", 0);
		this.CPllCtrl4_p3_CPllCpIntGsCtrl = this.CPllCtrl4_p3.CPllCpIntGsCtrl;
		this.CPllCpIntGsCtrl = this.CPllCtrl4_p3.CPllCpIntGsCtrl;
		this.CPllCtrl4_p3_CReservedPllCpIntGsCtrl = this.CPllCtrl4_p3.CReservedPllCpIntGsCtrl;
		this.CReservedPllCpIntGsCtrl = this.CPllCtrl4_p3.CReservedPllCpIntGsCtrl;
		this.CPllCtrl4_p3_CPllCpPropGsCtrl = this.CPllCtrl4_p3.CPllCpPropGsCtrl;
		this.CPllCpPropGsCtrl = this.CPllCtrl4_p3.CPllCpPropGsCtrl;
      this.CPllCtrl5_p3 = ral_reg_DWC_DDRPHYA_HMMAS0_p3_CPllCtrl5_p3::type_id::create("CPllCtrl5_p3",,get_full_name());
      if(this.CPllCtrl5_p3.has_coverage(UVM_CVR_ALL))
      	this.CPllCtrl5_p3.cg_bits.option.name = {get_name(), ".", "CPllCtrl5_p3_bits"};
      this.CPllCtrl5_p3.configure(this, null, "");
      this.CPllCtrl5_p3.build();
      this.default_map.add_reg(this.CPllCtrl5_p3, `UVM_REG_ADDR_WIDTH'h8, "RW", 0);
		this.CPllCtrl5_p3_CPllDivSel = this.CPllCtrl5_p3.CPllDivSel;
		this.CPllDivSel = this.CPllCtrl5_p3.CPllDivSel;
		this.CPllCtrl5_p3_CPllV2IMode = this.CPllCtrl5_p3.CPllV2IMode;
		this.CPllV2IMode = this.CPllCtrl5_p3.CPllV2IMode;
		this.CPllCtrl5_p3_CPllVcoLowFreq = this.CPllCtrl5_p3.CPllVcoLowFreq;
		this.CPllVcoLowFreq = this.CPllCtrl5_p3.CPllVcoLowFreq;
      this.CPllDacValIn_p3 = ral_reg_DWC_DDRPHYA_HMMAS0_p3_CPllDacValIn_p3::type_id::create("CPllDacValIn_p3",,get_full_name());
      if(this.CPllDacValIn_p3.has_coverage(UVM_CVR_ALL))
      	this.CPllDacValIn_p3.cg_bits.option.name = {get_name(), ".", "CPllDacValIn_p3_bits"};
      this.CPllDacValIn_p3.configure(this, null, "");
      this.CPllDacValIn_p3.build();
      this.default_map.add_reg(this.CPllDacValIn_p3, `UVM_REG_ADDR_WIDTH'h9, "RW", 0);
		this.CPllDacValIn_p3_CPllDacValIn_p3 = this.CPllDacValIn_p3.CPllDacValIn_p3;
      this.CMasterReserved_p3 = ral_reg_DWC_DDRPHYA_HMMAS0_p3_CMasterReserved_p3::type_id::create("CMasterReserved_p3",,get_full_name());
      if(this.CMasterReserved_p3.has_coverage(UVM_CVR_ALL))
      	this.CMasterReserved_p3.cg_bits.option.name = {get_name(), ".", "CMasterReserved_p3_bits"};
      this.CMasterReserved_p3.configure(this, null, "");
      this.CMasterReserved_p3.build();
      this.default_map.add_reg(this.CMasterReserved_p3, `UVM_REG_ADDR_WIDTH'hA, "RW", 0);
		this.CMasterReserved_p3_CMasterReserved_p3 = this.CMasterReserved_p3.CMasterReserved_p3;
      this.HMPclkPtrInitVal_p3 = ral_reg_DWC_DDRPHYA_HMMAS0_p3_HMPclkPtrInitVal_p3::type_id::create("HMPclkPtrInitVal_p3",,get_full_name());
      if(this.HMPclkPtrInitVal_p3.has_coverage(UVM_CVR_ALL))
      	this.HMPclkPtrInitVal_p3.cg_bits.option.name = {get_name(), ".", "HMPclkPtrInitVal_p3_bits"};
      this.HMPclkPtrInitVal_p3.configure(this, null, "");
      this.HMPclkPtrInitVal_p3.build();
      this.default_map.add_reg(this.HMPclkPtrInitVal_p3, `UVM_REG_ADDR_WIDTH'h40, "RW", 0);
		this.HMPclkPtrInitVal_p3_HMPclkPtrInitVal_p3 = this.HMPclkPtrInitVal_p3.HMPclkPtrInitVal_p3;
      this.HMReservedP1_p3 = ral_reg_DWC_DDRPHYA_HMMAS0_p3_HMReservedP1_p3::type_id::create("HMReservedP1_p3",,get_full_name());
      if(this.HMReservedP1_p3.has_coverage(UVM_CVR_ALL))
      	this.HMReservedP1_p3.cg_bits.option.name = {get_name(), ".", "HMReservedP1_p3_bits"};
      this.HMReservedP1_p3.configure(this, null, "");
      this.HMReservedP1_p3.build();
      this.default_map.add_reg(this.HMReservedP1_p3, `UVM_REG_ADDR_WIDTH'hFF, "RW", 0);
		this.HMReservedP1_p3_HMReservedP1_p3 = this.HMReservedP1_p3.HMReservedP1_p3;
   endfunction : build

	`uvm_object_utils(ral_block_DWC_DDRPHYA_HMMAS0_p3)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_DDRPHYA_HMMAS0_p3


endpackage
`endif
