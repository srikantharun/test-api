`ifndef RAL_DWC_DDRPHYA_ZCAL0_P0_PKG
`define RAL_DWC_DDRPHYA_ZCAL0_P0_PKG

package ral_DWC_DDRPHYA_ZCAL0_p0_pkg;
import uvm_pkg::*;

class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZcalClkDiv extends uvm_reg;
	rand uvm_reg_field ZcalClkDiv;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZcalClkDiv: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZcalClkDiv");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZcalClkDiv = uvm_reg_field::type_id::create("ZcalClkDiv",,get_full_name());
      this.ZcalClkDiv.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZcalClkDiv)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZcalClkDiv


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalClkInfo_p0 extends uvm_reg;
	rand uvm_reg_field ZCalDfiClkTicksPer1uS;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalDfiClkTicksPer1uS: coverpoint {m_data[10:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {12'b??????????00};
	      wildcard bins bit_0_wr_as_1 = {12'b??????????10};
	      wildcard bins bit_0_rd_as_0 = {12'b??????????01};
	      wildcard bins bit_0_rd_as_1 = {12'b??????????11};
	      wildcard bins bit_1_wr_as_0 = {12'b?????????0?0};
	      wildcard bins bit_1_wr_as_1 = {12'b?????????1?0};
	      wildcard bins bit_1_rd_as_0 = {12'b?????????0?1};
	      wildcard bins bit_1_rd_as_1 = {12'b?????????1?1};
	      wildcard bins bit_2_wr_as_0 = {12'b????????0??0};
	      wildcard bins bit_2_wr_as_1 = {12'b????????1??0};
	      wildcard bins bit_2_rd_as_0 = {12'b????????0??1};
	      wildcard bins bit_2_rd_as_1 = {12'b????????1??1};
	      wildcard bins bit_3_wr_as_0 = {12'b???????0???0};
	      wildcard bins bit_3_wr_as_1 = {12'b???????1???0};
	      wildcard bins bit_3_rd_as_0 = {12'b???????0???1};
	      wildcard bins bit_3_rd_as_1 = {12'b???????1???1};
	      wildcard bins bit_4_wr_as_0 = {12'b??????0????0};
	      wildcard bins bit_4_wr_as_1 = {12'b??????1????0};
	      wildcard bins bit_4_rd_as_0 = {12'b??????0????1};
	      wildcard bins bit_4_rd_as_1 = {12'b??????1????1};
	      wildcard bins bit_5_wr_as_0 = {12'b?????0?????0};
	      wildcard bins bit_5_wr_as_1 = {12'b?????1?????0};
	      wildcard bins bit_5_rd_as_0 = {12'b?????0?????1};
	      wildcard bins bit_5_rd_as_1 = {12'b?????1?????1};
	      wildcard bins bit_6_wr_as_0 = {12'b????0??????0};
	      wildcard bins bit_6_wr_as_1 = {12'b????1??????0};
	      wildcard bins bit_6_rd_as_0 = {12'b????0??????1};
	      wildcard bins bit_6_rd_as_1 = {12'b????1??????1};
	      wildcard bins bit_7_wr_as_0 = {12'b???0???????0};
	      wildcard bins bit_7_wr_as_1 = {12'b???1???????0};
	      wildcard bins bit_7_rd_as_0 = {12'b???0???????1};
	      wildcard bins bit_7_rd_as_1 = {12'b???1???????1};
	      wildcard bins bit_8_wr_as_0 = {12'b??0????????0};
	      wildcard bins bit_8_wr_as_1 = {12'b??1????????0};
	      wildcard bins bit_8_rd_as_0 = {12'b??0????????1};
	      wildcard bins bit_8_rd_as_1 = {12'b??1????????1};
	      wildcard bins bit_9_wr_as_0 = {12'b?0?????????0};
	      wildcard bins bit_9_wr_as_1 = {12'b?1?????????0};
	      wildcard bins bit_9_rd_as_0 = {12'b?0?????????1};
	      wildcard bins bit_9_rd_as_1 = {12'b?1?????????1};
	      wildcard bins bit_10_wr_as_0 = {12'b0??????????0};
	      wildcard bins bit_10_wr_as_1 = {12'b1??????????0};
	      wildcard bins bit_10_rd_as_0 = {12'b0??????????1};
	      wildcard bins bit_10_rd_as_1 = {12'b1??????????1};
	      option.weight = 44;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalClkInfo_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalDfiClkTicksPer1uS = uvm_reg_field::type_id::create("ZCalDfiClkTicksPer1uS",,get_full_name());
      this.ZCalDfiClkTicksPer1uS.configure(this, 11, 0, "RW", 0, 11'h320, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalClkInfo_p0)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalClkInfo_p0


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_MtestMuxSel extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_MtestMuxSel");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MtestMuxSel = uvm_reg_field::type_id::create("MtestMuxSel",,get_full_name());
      this.MtestMuxSel.configure(this, 10, 0, "RW", 0, 10'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_MtestMuxSel)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_MtestMuxSel


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCALParityInvert extends uvm_reg;
	rand uvm_reg_field ZCALParityInvert;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCALParityInvert: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCALParityInvert");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCALParityInvert = uvm_reg_field::type_id::create("ZCALParityInvert",,get_full_name());
      this.ZCALParityInvert.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCALParityInvert)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCALParityInvert


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ScratchPadZCAL extends uvm_reg;
	rand uvm_reg_field ScratchPadZCAL;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ScratchPadZCAL: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ScratchPadZCAL");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ScratchPadZCAL = uvm_reg_field::type_id::create("ScratchPadZCAL",,get_full_name());
      this.ScratchPadZCAL.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ScratchPadZCAL)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ScratchPadZCAL


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCALReserved0 extends uvm_reg;
	rand uvm_reg_field ZCALReserved0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCALReserved0: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCALReserved0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCALReserved0 = uvm_reg_field::type_id::create("ZCALReserved0",,get_full_name());
      this.ZCALReserved0.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCALReserved0)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCALReserved0


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_PUBReservedP1_p0 extends uvm_reg;
	rand uvm_reg_field PUBReservedP1_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PUBReservedP1_p0: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_PUBReservedP1_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PUBReservedP1_p0 = uvm_reg_field::type_id::create("PUBReservedP1_p0",,get_full_name());
      this.PUBReservedP1_p0.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_PUBReservedP1_p0)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_PUBReservedP1_p0


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalBaseCtrl extends uvm_reg;
	rand uvm_reg_field ZCalBasePU;
	rand uvm_reg_field ZCalBasePD;
	rand uvm_reg_field ReservedZCalBase;
	rand uvm_reg_field ZCalTxModeCtl;
	rand uvm_reg_field ReservedZCalTxModeCtl;
	rand uvm_reg_field ZCalClkDis;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalBasePU: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ZCalBasePD: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ReservedZCalBase: coverpoint {m_data[3:2], m_is_read} iff(m_be) {
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
	   ZCalTxModeCtl: coverpoint {m_data[6:4], m_is_read} iff(m_be) {
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
	   ReservedZCalTxModeCtl: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ZCalClkDis: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalBaseCtrl");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalBasePU = uvm_reg_field::type_id::create("ZCalBasePU",,get_full_name());
      this.ZCalBasePU.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 0);
      this.ZCalBasePD = uvm_reg_field::type_id::create("ZCalBasePD",,get_full_name());
      this.ZCalBasePD.configure(this, 1, 1, "RW", 0, 1'h1, 1, 0, 0);
      this.ReservedZCalBase = uvm_reg_field::type_id::create("ReservedZCalBase",,get_full_name());
      this.ReservedZCalBase.configure(this, 2, 2, "RW", 0, 2'h0, 1, 0, 0);
      this.ZCalTxModeCtl = uvm_reg_field::type_id::create("ZCalTxModeCtl",,get_full_name());
      this.ZCalTxModeCtl.configure(this, 3, 4, "RW", 0, 3'h0, 1, 0, 0);
      this.ReservedZCalTxModeCtl = uvm_reg_field::type_id::create("ReservedZCalTxModeCtl",,get_full_name());
      this.ReservedZCalTxModeCtl.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ZCalClkDis = uvm_reg_field::type_id::create("ZCalClkDis",,get_full_name());
      this.ZCalClkDis.configure(this, 1, 8, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalBaseCtrl)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalBaseCtrl


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalRate extends uvm_reg;
	rand uvm_reg_field ZCalInterval;
	rand uvm_reg_field ZCalOnce;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalInterval: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   ZCalOnce: coverpoint {m_data[4:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalRate");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalInterval = uvm_reg_field::type_id::create("ZCalInterval",,get_full_name());
      this.ZCalInterval.configure(this, 4, 0, "RW", 0, 4'h9, 1, 0, 0);
      this.ZCalOnce = uvm_reg_field::type_id::create("ZCalOnce",,get_full_name());
      this.ZCalOnce.configure(this, 1, 4, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalRate)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalRate


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCtrl extends uvm_reg;
	rand uvm_reg_field ReservedZCalCancelRoundErrDis;
	rand uvm_reg_field ReservedZCalSlowComp;
	rand uvm_reg_field ZCalPURoundUp;
	rand uvm_reg_field ZCalPDRoundUp;
	rand uvm_reg_field ZCalMaxTestsNumber;
	rand uvm_reg_field ZCalDoubleLoopEn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ReservedZCalCancelRoundErrDis: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ReservedZCalSlowComp: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ZCalPURoundUp: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ZCalPDRoundUp: coverpoint {m_data[3:3], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ZCalMaxTestsNumber: coverpoint {m_data[12:4], m_is_read} iff(m_be) {
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
	   ZCalDoubleLoopEn: coverpoint {m_data[13:13], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalCtrl");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ReservedZCalCancelRoundErrDis = uvm_reg_field::type_id::create("ReservedZCalCancelRoundErrDis",,get_full_name());
      this.ReservedZCalCancelRoundErrDis.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 0);
      this.ReservedZCalSlowComp = uvm_reg_field::type_id::create("ReservedZCalSlowComp",,get_full_name());
      this.ReservedZCalSlowComp.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.ZCalPURoundUp = uvm_reg_field::type_id::create("ZCalPURoundUp",,get_full_name());
      this.ZCalPURoundUp.configure(this, 1, 2, "RW", 0, 1'h1, 1, 0, 0);
      this.ZCalPDRoundUp = uvm_reg_field::type_id::create("ZCalPDRoundUp",,get_full_name());
      this.ZCalPDRoundUp.configure(this, 1, 3, "RW", 0, 1'h1, 1, 0, 0);
      this.ZCalMaxTestsNumber = uvm_reg_field::type_id::create("ZCalMaxTestsNumber",,get_full_name());
      this.ZCalMaxTestsNumber.configure(this, 9, 4, "RW", 0, 9'h1ff, 1, 0, 0);
      this.ZCalDoubleLoopEn = uvm_reg_field::type_id::create("ZCalDoubleLoopEn",,get_full_name());
      this.ZCalDoubleLoopEn.configure(this, 1, 13, "RW", 0, 1'h1, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCtrl)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCtrl


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompInvert extends uvm_reg;
	rand uvm_reg_field ZCalCompInvertComp;
	rand uvm_reg_field ZCalCompInvertPU;
	rand uvm_reg_field ZCalCompInvertPD;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalCompInvertComp: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ZCalCompInvertPU: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ZCalCompInvertPD: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalCompInvert");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalCompInvertComp = uvm_reg_field::type_id::create("ZCalCompInvertComp",,get_full_name());
      this.ZCalCompInvertComp.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 0);
      this.ZCalCompInvertPU = uvm_reg_field::type_id::create("ZCalCompInvertPU",,get_full_name());
      this.ZCalCompInvertPU.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.ZCalCompInvertPD = uvm_reg_field::type_id::create("ZCalCompInvertPD",,get_full_name());
      this.ZCalCompInvertPD.configure(this, 1, 2, "RW", 0, 1'h1, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompInvert)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompInvert


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompOffset extends uvm_reg;
	rand uvm_reg_field ZCalCompOffsetVal;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalCompOffsetVal: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalCompOffset");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalCompOffsetVal = uvm_reg_field::type_id::create("ZCalCompOffsetVal",,get_full_name());
      this.ZCalCompOffsetVal.configure(this, 6, 0, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompOffset)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompOffset


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUOffset extends uvm_reg;
	rand uvm_reg_field ZCalPUOffsetVal;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalPUOffsetVal: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalPUOffset");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalPUOffsetVal = uvm_reg_field::type_id::create("ZCalPUOffsetVal",,get_full_name());
      this.ZCalPUOffsetVal.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUOffset)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUOffset


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompOvr extends uvm_reg;
	rand uvm_reg_field ZCalCompOvrEn;
	rand uvm_reg_field ReservedZCalCompOvrEn;
	rand uvm_reg_field ZCalCompOvrVal;
	rand uvm_reg_field ReservedZCalCompOvrVal;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalCompOvrEn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ReservedZCalCompOvrEn: coverpoint {m_data[7:1], m_is_read} iff(m_be) {
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
	   ZCalCompOvrVal: coverpoint {m_data[14:8], m_is_read} iff(m_be) {
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
	   ReservedZCalCompOvrVal: coverpoint {m_data[15:15], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalCompOvr");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalCompOvrEn = uvm_reg_field::type_id::create("ZCalCompOvrEn",,get_full_name());
      this.ZCalCompOvrEn.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.ReservedZCalCompOvrEn = uvm_reg_field::type_id::create("ReservedZCalCompOvrEn",,get_full_name());
      this.ReservedZCalCompOvrEn.configure(this, 7, 1, "RW", 0, 7'h0, 1, 0, 0);
      this.ZCalCompOvrVal = uvm_reg_field::type_id::create("ZCalCompOvrVal",,get_full_name());
      this.ZCalCompOvrVal.configure(this, 7, 8, "RW", 0, 7'h0, 1, 0, 0);
      this.ReservedZCalCompOvrVal = uvm_reg_field::type_id::create("ReservedZCalCompOvrVal",,get_full_name());
      this.ReservedZCalCompOvrVal.configure(this, 1, 15, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompOvr)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompOvr


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUOvr extends uvm_reg;
	rand uvm_reg_field ZCalPUOvrEn;
	rand uvm_reg_field ReservedZCalPUOvrEn;
	rand uvm_reg_field ZCalPUOvrVal;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalPUOvrEn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ReservedZCalPUOvrEn: coverpoint {m_data[6:1], m_is_read} iff(m_be) {
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
	   ZCalPUOvrVal: coverpoint {m_data[15:7], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalPUOvr");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalPUOvrEn = uvm_reg_field::type_id::create("ZCalPUOvrEn",,get_full_name());
      this.ZCalPUOvrEn.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.ReservedZCalPUOvrEn = uvm_reg_field::type_id::create("ReservedZCalPUOvrEn",,get_full_name());
      this.ReservedZCalPUOvrEn.configure(this, 6, 1, "RW", 0, 6'h0, 1, 0, 0);
      this.ZCalPUOvrVal = uvm_reg_field::type_id::create("ZCalPUOvrVal",,get_full_name());
      this.ZCalPUOvrVal.configure(this, 9, 7, "RW", 0, 9'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUOvr)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUOvr


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalClrFirstRunDone extends uvm_reg;
	rand uvm_reg_field ZCalClrFirstRunDone;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalClrFirstRunDone: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalClrFirstRunDone");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalClrFirstRunDone = uvm_reg_field::type_id::create("ZCalClrFirstRunDone",,get_full_name());
      this.ZCalClrFirstRunDone.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalClrFirstRunDone)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalClrFirstRunDone


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPDSearchGainTV extends uvm_reg;
	rand uvm_reg_field ZCalPDSearchGainTVVal;
	rand uvm_reg_field ZCalPDSearchGainTVValB;
	rand uvm_reg_field ZCalPDSearchGainTVAuto;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalPDSearchGainTVVal: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   ZCalPDSearchGainTVValB: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   ZCalPDSearchGainTVAuto: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalPDSearchGainTV");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalPDSearchGainTVVal = uvm_reg_field::type_id::create("ZCalPDSearchGainTVVal",,get_full_name());
      this.ZCalPDSearchGainTVVal.configure(this, 4, 0, "RW", 0, 4'h8, 1, 0, 0);
      this.ZCalPDSearchGainTVValB = uvm_reg_field::type_id::create("ZCalPDSearchGainTVValB",,get_full_name());
      this.ZCalPDSearchGainTVValB.configure(this, 4, 4, "RW", 0, 4'h8, 1, 0, 0);
      this.ZCalPDSearchGainTVAuto = uvm_reg_field::type_id::create("ZCalPDSearchGainTVAuto",,get_full_name());
      this.ZCalPDSearchGainTVAuto.configure(this, 1, 8, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPDSearchGainTV)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPDSearchGainTV


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalAnaSettlingTime extends uvm_reg;
	rand uvm_reg_field ZCalAnaSettlingTime;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalAnaSettlingTime: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalAnaSettlingTime");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalAnaSettlingTime = uvm_reg_field::type_id::create("ZCalAnaSettlingTime",,get_full_name());
      this.ZCalAnaSettlingTime.configure(this, 6, 0, "RW", 0, 6'h10, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalAnaSettlingTime)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalAnaSettlingTime


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalReset extends uvm_reg;
	rand uvm_reg_field ZCalReset;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalReset: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalReset");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalReset = uvm_reg_field::type_id::create("ZCalReset",,get_full_name());
      this.ZCalReset.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalReset)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalReset


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalRun extends uvm_reg;
	rand uvm_reg_field ZCalRun;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalRun: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalRun");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalRun = uvm_reg_field::type_id::create("ZCalRun",,get_full_name());
      this.ZCalRun.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalRun)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalRun


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalBusy extends uvm_reg;
	uvm_reg_field ZCalBusy;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalBusy: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalBusy");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalBusy = uvm_reg_field::type_id::create("ZCalBusy",,get_full_name());
      this.ZCalBusy.configure(this, 1, 0, "RO", 1, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalBusy)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalBusy


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompResult extends uvm_reg;
	uvm_reg_field ZCalCompResult;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalCompResult: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalCompResult");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalCompResult = uvm_reg_field::type_id::create("ZCalCompResult",,get_full_name());
      this.ZCalCompResult.configure(this, 7, 0, "RO", 1, 7'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompResult)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompResult


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUResult extends uvm_reg;
	uvm_reg_field ZCalPUResult;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalPUResult: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalPUResult");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalPUResult = uvm_reg_field::type_id::create("ZCalPUResult",,get_full_name());
      this.ZCalPUResult.configure(this, 9, 0, "RO", 1, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUResult)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUResult


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPDResult extends uvm_reg;
	uvm_reg_field ZCalPDResult;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalPDResult: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalPDResult");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalPDResult = uvm_reg_field::type_id::create("ZCalPDResult",,get_full_name());
      this.ZCalPDResult.configure(this, 9, 0, "RO", 1, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPDResult)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPDResult


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCodePU extends uvm_reg;
	uvm_reg_field ZCalCodePU;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalCodePU: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalCodePU");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalCodePU = uvm_reg_field::type_id::create("ZCalCodePU",,get_full_name());
      this.ZCalCodePU.configure(this, 9, 0, "RO", 1, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCodePU)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCodePU


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCodePD extends uvm_reg;
	uvm_reg_field ZCalCodePD;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalCodePD: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalCodePD");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalCodePD = uvm_reg_field::type_id::create("ZCalCodePD",,get_full_name());
      this.ZCalCodePD.configure(this, 9, 0, "RO", 1, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCodePD)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCodePD


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompSearchSeed extends uvm_reg;
	rand uvm_reg_field ZCalCompSearchSeedVal;
	rand uvm_reg_field ReservedZCalCompSearchSeedVal;
	rand uvm_reg_field ZCalCompSearchSeedAuto;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalCompSearchSeedVal: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   ReservedZCalCompSearchSeedVal: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ZCalCompSearchSeedAuto: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalCompSearchSeed");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalCompSearchSeedVal = uvm_reg_field::type_id::create("ZCalCompSearchSeedVal",,get_full_name());
      this.ZCalCompSearchSeedVal.configure(this, 7, 0, "RW", 0, 7'h40, 1, 0, 0);
      this.ReservedZCalCompSearchSeedVal = uvm_reg_field::type_id::create("ReservedZCalCompSearchSeedVal",,get_full_name());
      this.ReservedZCalCompSearchSeedVal.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ZCalCompSearchSeedAuto = uvm_reg_field::type_id::create("ZCalCompSearchSeedAuto",,get_full_name());
      this.ZCalCompSearchSeedAuto.configure(this, 1, 8, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompSearchSeed)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompSearchSeed


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUSearchSeed extends uvm_reg;
	rand uvm_reg_field ZCalPUSearchSeedVal;
	rand uvm_reg_field ZCalPUSearchSeedAuto;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalPUSearchSeedVal: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	   ZCalPUSearchSeedAuto: coverpoint {m_data[9:9], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalPUSearchSeed");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalPUSearchSeedVal = uvm_reg_field::type_id::create("ZCalPUSearchSeedVal",,get_full_name());
      this.ZCalPUSearchSeedVal.configure(this, 9, 0, "RW", 0, 9'h80, 1, 0, 0);
      this.ZCalPUSearchSeedAuto = uvm_reg_field::type_id::create("ZCalPUSearchSeedAuto",,get_full_name());
      this.ZCalPUSearchSeedAuto.configure(this, 1, 9, "RW", 0, 1'h1, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUSearchSeed)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUSearchSeed


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPDSearchSeed extends uvm_reg;
	rand uvm_reg_field ZCalPDSearchSeedVal;
	rand uvm_reg_field ZCalPDSearchSeedAuto;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalPDSearchSeedVal: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	   ZCalPDSearchSeedAuto: coverpoint {m_data[9:9], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalPDSearchSeed");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalPDSearchSeedVal = uvm_reg_field::type_id::create("ZCalPDSearchSeedVal",,get_full_name());
      this.ZCalPDSearchSeedVal.configure(this, 9, 0, "RW", 0, 9'h80, 1, 0, 0);
      this.ZCalPDSearchSeedAuto = uvm_reg_field::type_id::create("ZCalPDSearchSeedAuto",,get_full_name());
      this.ZCalPDSearchSeedAuto.configure(this, 1, 9, "RW", 0, 1'h1, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPDSearchSeed)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPDSearchSeed


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompSearchGainIV extends uvm_reg;
	rand uvm_reg_field ZCalCompSearchGainIVVal;
	rand uvm_reg_field ZCalCompSearchGainIVValB;
	rand uvm_reg_field ZCalCompSearchGainIVAuto;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalCompSearchGainIVVal: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   ZCalCompSearchGainIVValB: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   ZCalCompSearchGainIVAuto: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalCompSearchGainIV");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalCompSearchGainIVVal = uvm_reg_field::type_id::create("ZCalCompSearchGainIVVal",,get_full_name());
      this.ZCalCompSearchGainIVVal.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.ZCalCompSearchGainIVValB = uvm_reg_field::type_id::create("ZCalCompSearchGainIVValB",,get_full_name());
      this.ZCalCompSearchGainIVValB.configure(this, 4, 4, "RW", 0, 4'h3, 1, 0, 0);
      this.ZCalCompSearchGainIVAuto = uvm_reg_field::type_id::create("ZCalCompSearchGainIVAuto",,get_full_name());
      this.ZCalCompSearchGainIVAuto.configure(this, 1, 8, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompSearchGainIV)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompSearchGainIV


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompSearchGainTV extends uvm_reg;
	rand uvm_reg_field ZCalCompSearchGainTVVal;
	rand uvm_reg_field ZCalCompSearchGainTVValB;
	rand uvm_reg_field ZCalCompSearchGainTVAuto;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalCompSearchGainTVVal: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   ZCalCompSearchGainTVValB: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   ZCalCompSearchGainTVAuto: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalCompSearchGainTV");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalCompSearchGainTVVal = uvm_reg_field::type_id::create("ZCalCompSearchGainTVVal",,get_full_name());
      this.ZCalCompSearchGainTVVal.configure(this, 4, 0, "RW", 0, 4'h8, 1, 0, 0);
      this.ZCalCompSearchGainTVValB = uvm_reg_field::type_id::create("ZCalCompSearchGainTVValB",,get_full_name());
      this.ZCalCompSearchGainTVValB.configure(this, 4, 4, "RW", 0, 4'h8, 1, 0, 0);
      this.ZCalCompSearchGainTVAuto = uvm_reg_field::type_id::create("ZCalCompSearchGainTVAuto",,get_full_name());
      this.ZCalCompSearchGainTVAuto.configure(this, 1, 8, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompSearchGainTV)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompSearchGainTV


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUSearchGainIV extends uvm_reg;
	rand uvm_reg_field ZCalPUSearchGainIVVal;
	rand uvm_reg_field ZCalPUSearchGainIVValB;
	rand uvm_reg_field ZCalPUSearchGainIVAuto;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalPUSearchGainIVVal: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   ZCalPUSearchGainIVValB: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   ZCalPUSearchGainIVAuto: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalPUSearchGainIV");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalPUSearchGainIVVal = uvm_reg_field::type_id::create("ZCalPUSearchGainIVVal",,get_full_name());
      this.ZCalPUSearchGainIVVal.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.ZCalPUSearchGainIVValB = uvm_reg_field::type_id::create("ZCalPUSearchGainIVValB",,get_full_name());
      this.ZCalPUSearchGainIVValB.configure(this, 4, 4, "RW", 0, 4'h3, 1, 0, 0);
      this.ZCalPUSearchGainIVAuto = uvm_reg_field::type_id::create("ZCalPUSearchGainIVAuto",,get_full_name());
      this.ZCalPUSearchGainIVAuto.configure(this, 1, 8, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUSearchGainIV)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUSearchGainIV


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUSearchGainTV extends uvm_reg;
	rand uvm_reg_field ZCalPUSearchGainTVVal;
	rand uvm_reg_field ZCalPUSearchGainTVValB;
	rand uvm_reg_field ZCalPUSearchGainTVAuto;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalPUSearchGainTVVal: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   ZCalPUSearchGainTVValB: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   ZCalPUSearchGainTVAuto: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalPUSearchGainTV");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalPUSearchGainTVVal = uvm_reg_field::type_id::create("ZCalPUSearchGainTVVal",,get_full_name());
      this.ZCalPUSearchGainTVVal.configure(this, 4, 0, "RW", 0, 4'h8, 1, 0, 0);
      this.ZCalPUSearchGainTVValB = uvm_reg_field::type_id::create("ZCalPUSearchGainTVValB",,get_full_name());
      this.ZCalPUSearchGainTVValB.configure(this, 4, 4, "RW", 0, 4'h8, 1, 0, 0);
      this.ZCalPUSearchGainTVAuto = uvm_reg_field::type_id::create("ZCalPUSearchGainTVAuto",,get_full_name());
      this.ZCalPUSearchGainTVAuto.configure(this, 1, 8, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUSearchGainTV)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUSearchGainTV


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPDSearchGainIV extends uvm_reg;
	rand uvm_reg_field ZCalPDSearchGainIVVal;
	rand uvm_reg_field ZCalPDSearchGainIVValB;
	rand uvm_reg_field ZCalPDSearchGainIVAuto;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalPDSearchGainIVVal: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   ZCalPDSearchGainIVValB: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   ZCalPDSearchGainIVAuto: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalPDSearchGainIV");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalPDSearchGainIVVal = uvm_reg_field::type_id::create("ZCalPDSearchGainIVVal",,get_full_name());
      this.ZCalPDSearchGainIVVal.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.ZCalPDSearchGainIVValB = uvm_reg_field::type_id::create("ZCalPDSearchGainIVValB",,get_full_name());
      this.ZCalPDSearchGainIVValB.configure(this, 4, 4, "RW", 0, 4'h3, 1, 0, 0);
      this.ZCalPDSearchGainIVAuto = uvm_reg_field::type_id::create("ZCalPDSearchGainIVAuto",,get_full_name());
      this.ZCalPDSearchGainIVAuto.configure(this, 1, 8, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPDSearchGainIV)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPDSearchGainIV


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQUpdate extends uvm_reg;
	rand uvm_reg_field ZQUpdate;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZQUpdate: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZQUpdate");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZQUpdate = uvm_reg_field::type_id::create("ZQUpdate",,get_full_name());
      this.ZQUpdate.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQUpdate)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQUpdate


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUch0 extends uvm_reg;
	rand uvm_reg_field ZQCalCodePUch0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZQCalCodePUch0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUch0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZQCalCodePUch0 = uvm_reg_field::type_id::create("ZQCalCodePUch0",,get_full_name());
      this.ZQCalCodePUch0.configure(this, 9, 0, "RW", 0, 9'h180, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUch0)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUch0


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDch0 extends uvm_reg;
	rand uvm_reg_field ZQCalCodePDch0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZQCalCodePDch0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDch0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZQCalCodePDch0 = uvm_reg_field::type_id::create("ZQCalCodePDch0",,get_full_name());
      this.ZQCalCodePDch0.configure(this, 9, 0, "RW", 0, 9'h180, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDch0)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDch0


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalBaseCtrl extends uvm_reg;
	rand uvm_reg_field ZQCalBasePU;
	rand uvm_reg_field ZQCalBasePD;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZQCalBasePU: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ZQCalBasePD: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZQCalBaseCtrl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZQCalBasePU = uvm_reg_field::type_id::create("ZQCalBasePU",,get_full_name());
      this.ZQCalBasePU.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 0);
      this.ZQCalBasePD = uvm_reg_field::type_id::create("ZQCalBasePD",,get_full_name());
      this.ZQCalBasePD.configure(this, 1, 1, "RW", 0, 1'h1, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalBaseCtrl)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalBaseCtrl


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOffsetPU extends uvm_reg;
	rand uvm_reg_field ZQCalCodeOffsetValPU;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZQCalCodeOffsetValPU: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOffsetPU");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZQCalCodeOffsetValPU = uvm_reg_field::type_id::create("ZQCalCodeOffsetValPU",,get_full_name());
      this.ZQCalCodeOffsetValPU.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOffsetPU)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOffsetPU


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOffsetPD extends uvm_reg;
	rand uvm_reg_field ZQCalCodeOffsetValPD;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZQCalCodeOffsetValPD: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOffsetPD");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZQCalCodeOffsetValPD = uvm_reg_field::type_id::create("ZQCalCodeOffsetValPD",,get_full_name());
      this.ZQCalCodeOffsetValPD.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOffsetPD)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOffsetPD


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOvrPU extends uvm_reg;
	rand uvm_reg_field ZQCalCodeOvrEnPU;
	rand uvm_reg_field ReservedZQCalCodeOvrEnPU;
	rand uvm_reg_field ZQCalCodeOvrValPU;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZQCalCodeOvrEnPU: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ReservedZQCalCodeOvrEnPU: coverpoint {m_data[6:1], m_is_read} iff(m_be) {
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
	   ZQCalCodeOvrValPU: coverpoint {m_data[15:7], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOvrPU");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZQCalCodeOvrEnPU = uvm_reg_field::type_id::create("ZQCalCodeOvrEnPU",,get_full_name());
      this.ZQCalCodeOvrEnPU.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.ReservedZQCalCodeOvrEnPU = uvm_reg_field::type_id::create("ReservedZQCalCodeOvrEnPU",,get_full_name());
      this.ReservedZQCalCodeOvrEnPU.configure(this, 6, 1, "RW", 0, 6'h0, 1, 0, 0);
      this.ZQCalCodeOvrValPU = uvm_reg_field::type_id::create("ZQCalCodeOvrValPU",,get_full_name());
      this.ZQCalCodeOvrValPU.configure(this, 9, 7, "RW", 0, 9'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOvrPU)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOvrPU


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOvrPD extends uvm_reg;
	rand uvm_reg_field ZQCalCodeOvrEnPD;
	rand uvm_reg_field ReservedZQCalCodeOvrEnPD;
	rand uvm_reg_field ZQCalCodeOvrValPD;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZQCalCodeOvrEnPD: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ReservedZQCalCodeOvrEnPD: coverpoint {m_data[6:1], m_is_read} iff(m_be) {
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
	   ZQCalCodeOvrValPD: coverpoint {m_data[15:7], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOvrPD");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZQCalCodeOvrEnPD = uvm_reg_field::type_id::create("ZQCalCodeOvrEnPD",,get_full_name());
      this.ZQCalCodeOvrEnPD.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.ReservedZQCalCodeOvrEnPD = uvm_reg_field::type_id::create("ReservedZQCalCodeOvrEnPD",,get_full_name());
      this.ReservedZQCalCodeOvrEnPD.configure(this, 6, 1, "RW", 0, 6'h0, 1, 0, 0);
      this.ZQCalCodeOvrValPD = uvm_reg_field::type_id::create("ZQCalCodeOvrValPD",,get_full_name());
      this.ZQCalCodeOvrValPD.configure(this, 9, 7, "RW", 0, 9'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOvrPD)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOvrPD


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUMax extends uvm_reg;
	rand uvm_reg_field ZQCalCodePUMax;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZQCalCodePUMax: coverpoint {m_data[9:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUMax");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZQCalCodePUMax = uvm_reg_field::type_id::create("ZQCalCodePUMax",,get_full_name());
      this.ZQCalCodePUMax.configure(this, 10, 0, "RW", 0, 10'h1ff, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUMax)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUMax


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUMin extends uvm_reg;
	rand uvm_reg_field ZQCalCodePUMin;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZQCalCodePUMin: coverpoint {m_data[9:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUMin");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZQCalCodePUMin = uvm_reg_field::type_id::create("ZQCalCodePUMin",,get_full_name());
      this.ZQCalCodePUMin.configure(this, 10, 0, "RW", 0, 10'h100, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUMin)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUMin


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDMax extends uvm_reg;
	rand uvm_reg_field ZQCalCodePDMax;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZQCalCodePDMax: coverpoint {m_data[9:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDMax");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZQCalCodePDMax = uvm_reg_field::type_id::create("ZQCalCodePDMax",,get_full_name());
      this.ZQCalCodePDMax.configure(this, 10, 0, "RW", 0, 10'h1ff, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDMax)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDMax


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDMin extends uvm_reg;
	rand uvm_reg_field ZQCalCodePDMin;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZQCalCodePDMin: coverpoint {m_data[9:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDMin");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZQCalCodePDMin = uvm_reg_field::type_id::create("ZQCalCodePDMin",,get_full_name());
      this.ZQCalCodePDMin.configure(this, 10, 0, "RW", 0, 10'h100, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDMin)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDMin


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUch1 extends uvm_reg;
	rand uvm_reg_field ZQCalCodePUch1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZQCalCodePUch1: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUch1");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZQCalCodePUch1 = uvm_reg_field::type_id::create("ZQCalCodePUch1",,get_full_name());
      this.ZQCalCodePUch1.configure(this, 9, 0, "RW", 0, 9'h180, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUch1)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUch1


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDch1 extends uvm_reg;
	rand uvm_reg_field ZQCalCodePDch1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZQCalCodePDch1: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDch1");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZQCalCodePDch1 = uvm_reg_field::type_id::create("ZQCalCodePDch1",,get_full_name());
      this.ZQCalCodePDch1.configure(this, 9, 0, "RW", 0, 9'h180, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDch1)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDch1


class ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalStopClk_p0 extends uvm_reg;
	rand uvm_reg_field ZCalStopClk_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalStopClk_p0: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0_ZCalStopClk_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalStopClk_p0 = uvm_reg_field::type_id::create("ZCalStopClk_p0",,get_full_name());
      this.ZCalStopClk_p0.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalStopClk_p0)

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
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalStopClk_p0


class ral_block_DWC_DDRPHYA_ZCAL0_p0 extends uvm_reg_block;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZcalClkDiv ZcalClkDiv;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalClkInfo_p0 ZCalClkInfo_p0;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_MtestMuxSel MtestMuxSel;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCALParityInvert ZCALParityInvert;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ScratchPadZCAL ScratchPadZCAL;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCALReserved0 ZCALReserved0;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_PUBReservedP1_p0 PUBReservedP1_p0;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalBaseCtrl ZCalBaseCtrl;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalRate ZCalRate;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCtrl ZCalCtrl;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompInvert ZCalCompInvert;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompOffset ZCalCompOffset;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUOffset ZCalPUOffset;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompOvr ZCalCompOvr;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUOvr ZCalPUOvr;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalClrFirstRunDone ZCalClrFirstRunDone;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPDSearchGainTV ZCalPDSearchGainTV;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalAnaSettlingTime ZCalAnaSettlingTime;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalReset ZCalReset;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalRun ZCalRun;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalBusy ZCalBusy;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompResult ZCalCompResult;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUResult ZCalPUResult;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPDResult ZCalPDResult;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCodePU ZCalCodePU;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCodePD ZCalCodePD;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompSearchSeed ZCalCompSearchSeed;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUSearchSeed ZCalPUSearchSeed;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPDSearchSeed ZCalPDSearchSeed;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompSearchGainIV ZCalCompSearchGainIV;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompSearchGainTV ZCalCompSearchGainTV;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUSearchGainIV ZCalPUSearchGainIV;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUSearchGainTV ZCalPUSearchGainTV;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPDSearchGainIV ZCalPDSearchGainIV;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQUpdate ZQUpdate;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUch0 ZQCalCodePUch0;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDch0 ZQCalCodePDch0;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalBaseCtrl ZQCalBaseCtrl;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOffsetPU ZQCalCodeOffsetPU;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOffsetPD ZQCalCodeOffsetPD;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOvrPU ZQCalCodeOvrPU;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOvrPD ZQCalCodeOvrPD;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUMax ZQCalCodePUMax;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUMin ZQCalCodePUMin;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDMax ZQCalCodePDMax;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDMin ZQCalCodePDMin;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUch1 ZQCalCodePUch1;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDch1 ZQCalCodePDch1;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalStopClk_p0 ZCalStopClk_p0;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field ZcalClkDiv_ZcalClkDiv;
	rand uvm_reg_field ZCalClkInfo_p0_ZCalDfiClkTicksPer1uS;
	rand uvm_reg_field ZCalDfiClkTicksPer1uS;
	rand uvm_reg_field MtestMuxSel_MtestMuxSel;
	rand uvm_reg_field ZCALParityInvert_ZCALParityInvert;
	rand uvm_reg_field ScratchPadZCAL_ScratchPadZCAL;
	rand uvm_reg_field ZCALReserved0_ZCALReserved0;
	rand uvm_reg_field PUBReservedP1_p0_PUBReservedP1_p0;
	rand uvm_reg_field ZCalBaseCtrl_ZCalBasePU;
	rand uvm_reg_field ZCalBasePU;
	rand uvm_reg_field ZCalBaseCtrl_ZCalBasePD;
	rand uvm_reg_field ZCalBasePD;
	rand uvm_reg_field ZCalBaseCtrl_ReservedZCalBase;
	rand uvm_reg_field ReservedZCalBase;
	rand uvm_reg_field ZCalBaseCtrl_ZCalTxModeCtl;
	rand uvm_reg_field ZCalTxModeCtl;
	rand uvm_reg_field ZCalBaseCtrl_ReservedZCalTxModeCtl;
	rand uvm_reg_field ReservedZCalTxModeCtl;
	rand uvm_reg_field ZCalBaseCtrl_ZCalClkDis;
	rand uvm_reg_field ZCalClkDis;
	rand uvm_reg_field ZCalRate_ZCalInterval;
	rand uvm_reg_field ZCalInterval;
	rand uvm_reg_field ZCalRate_ZCalOnce;
	rand uvm_reg_field ZCalOnce;
	rand uvm_reg_field ZCalCtrl_ReservedZCalCancelRoundErrDis;
	rand uvm_reg_field ReservedZCalCancelRoundErrDis;
	rand uvm_reg_field ZCalCtrl_ReservedZCalSlowComp;
	rand uvm_reg_field ReservedZCalSlowComp;
	rand uvm_reg_field ZCalCtrl_ZCalPURoundUp;
	rand uvm_reg_field ZCalPURoundUp;
	rand uvm_reg_field ZCalCtrl_ZCalPDRoundUp;
	rand uvm_reg_field ZCalPDRoundUp;
	rand uvm_reg_field ZCalCtrl_ZCalMaxTestsNumber;
	rand uvm_reg_field ZCalMaxTestsNumber;
	rand uvm_reg_field ZCalCtrl_ZCalDoubleLoopEn;
	rand uvm_reg_field ZCalDoubleLoopEn;
	rand uvm_reg_field ZCalCompInvert_ZCalCompInvertComp;
	rand uvm_reg_field ZCalCompInvertComp;
	rand uvm_reg_field ZCalCompInvert_ZCalCompInvertPU;
	rand uvm_reg_field ZCalCompInvertPU;
	rand uvm_reg_field ZCalCompInvert_ZCalCompInvertPD;
	rand uvm_reg_field ZCalCompInvertPD;
	rand uvm_reg_field ZCalCompOffset_ZCalCompOffsetVal;
	rand uvm_reg_field ZCalCompOffsetVal;
	rand uvm_reg_field ZCalPUOffset_ZCalPUOffsetVal;
	rand uvm_reg_field ZCalPUOffsetVal;
	rand uvm_reg_field ZCalCompOvr_ZCalCompOvrEn;
	rand uvm_reg_field ZCalCompOvrEn;
	rand uvm_reg_field ZCalCompOvr_ReservedZCalCompOvrEn;
	rand uvm_reg_field ReservedZCalCompOvrEn;
	rand uvm_reg_field ZCalCompOvr_ZCalCompOvrVal;
	rand uvm_reg_field ZCalCompOvrVal;
	rand uvm_reg_field ZCalCompOvr_ReservedZCalCompOvrVal;
	rand uvm_reg_field ReservedZCalCompOvrVal;
	rand uvm_reg_field ZCalPUOvr_ZCalPUOvrEn;
	rand uvm_reg_field ZCalPUOvrEn;
	rand uvm_reg_field ZCalPUOvr_ReservedZCalPUOvrEn;
	rand uvm_reg_field ReservedZCalPUOvrEn;
	rand uvm_reg_field ZCalPUOvr_ZCalPUOvrVal;
	rand uvm_reg_field ZCalPUOvrVal;
	rand uvm_reg_field ZCalClrFirstRunDone_ZCalClrFirstRunDone;
	rand uvm_reg_field ZCalPDSearchGainTV_ZCalPDSearchGainTVVal;
	rand uvm_reg_field ZCalPDSearchGainTVVal;
	rand uvm_reg_field ZCalPDSearchGainTV_ZCalPDSearchGainTVValB;
	rand uvm_reg_field ZCalPDSearchGainTVValB;
	rand uvm_reg_field ZCalPDSearchGainTV_ZCalPDSearchGainTVAuto;
	rand uvm_reg_field ZCalPDSearchGainTVAuto;
	rand uvm_reg_field ZCalAnaSettlingTime_ZCalAnaSettlingTime;
	rand uvm_reg_field ZCalReset_ZCalReset;
	rand uvm_reg_field ZCalRun_ZCalRun;
	uvm_reg_field ZCalBusy_ZCalBusy;
	uvm_reg_field ZCalCompResult_ZCalCompResult;
	uvm_reg_field ZCalPUResult_ZCalPUResult;
	uvm_reg_field ZCalPDResult_ZCalPDResult;
	uvm_reg_field ZCalCodePU_ZCalCodePU;
	uvm_reg_field ZCalCodePD_ZCalCodePD;
	rand uvm_reg_field ZCalCompSearchSeed_ZCalCompSearchSeedVal;
	rand uvm_reg_field ZCalCompSearchSeedVal;
	rand uvm_reg_field ZCalCompSearchSeed_ReservedZCalCompSearchSeedVal;
	rand uvm_reg_field ReservedZCalCompSearchSeedVal;
	rand uvm_reg_field ZCalCompSearchSeed_ZCalCompSearchSeedAuto;
	rand uvm_reg_field ZCalCompSearchSeedAuto;
	rand uvm_reg_field ZCalPUSearchSeed_ZCalPUSearchSeedVal;
	rand uvm_reg_field ZCalPUSearchSeedVal;
	rand uvm_reg_field ZCalPUSearchSeed_ZCalPUSearchSeedAuto;
	rand uvm_reg_field ZCalPUSearchSeedAuto;
	rand uvm_reg_field ZCalPDSearchSeed_ZCalPDSearchSeedVal;
	rand uvm_reg_field ZCalPDSearchSeedVal;
	rand uvm_reg_field ZCalPDSearchSeed_ZCalPDSearchSeedAuto;
	rand uvm_reg_field ZCalPDSearchSeedAuto;
	rand uvm_reg_field ZCalCompSearchGainIV_ZCalCompSearchGainIVVal;
	rand uvm_reg_field ZCalCompSearchGainIVVal;
	rand uvm_reg_field ZCalCompSearchGainIV_ZCalCompSearchGainIVValB;
	rand uvm_reg_field ZCalCompSearchGainIVValB;
	rand uvm_reg_field ZCalCompSearchGainIV_ZCalCompSearchGainIVAuto;
	rand uvm_reg_field ZCalCompSearchGainIVAuto;
	rand uvm_reg_field ZCalCompSearchGainTV_ZCalCompSearchGainTVVal;
	rand uvm_reg_field ZCalCompSearchGainTVVal;
	rand uvm_reg_field ZCalCompSearchGainTV_ZCalCompSearchGainTVValB;
	rand uvm_reg_field ZCalCompSearchGainTVValB;
	rand uvm_reg_field ZCalCompSearchGainTV_ZCalCompSearchGainTVAuto;
	rand uvm_reg_field ZCalCompSearchGainTVAuto;
	rand uvm_reg_field ZCalPUSearchGainIV_ZCalPUSearchGainIVVal;
	rand uvm_reg_field ZCalPUSearchGainIVVal;
	rand uvm_reg_field ZCalPUSearchGainIV_ZCalPUSearchGainIVValB;
	rand uvm_reg_field ZCalPUSearchGainIVValB;
	rand uvm_reg_field ZCalPUSearchGainIV_ZCalPUSearchGainIVAuto;
	rand uvm_reg_field ZCalPUSearchGainIVAuto;
	rand uvm_reg_field ZCalPUSearchGainTV_ZCalPUSearchGainTVVal;
	rand uvm_reg_field ZCalPUSearchGainTVVal;
	rand uvm_reg_field ZCalPUSearchGainTV_ZCalPUSearchGainTVValB;
	rand uvm_reg_field ZCalPUSearchGainTVValB;
	rand uvm_reg_field ZCalPUSearchGainTV_ZCalPUSearchGainTVAuto;
	rand uvm_reg_field ZCalPUSearchGainTVAuto;
	rand uvm_reg_field ZCalPDSearchGainIV_ZCalPDSearchGainIVVal;
	rand uvm_reg_field ZCalPDSearchGainIVVal;
	rand uvm_reg_field ZCalPDSearchGainIV_ZCalPDSearchGainIVValB;
	rand uvm_reg_field ZCalPDSearchGainIVValB;
	rand uvm_reg_field ZCalPDSearchGainIV_ZCalPDSearchGainIVAuto;
	rand uvm_reg_field ZCalPDSearchGainIVAuto;
	rand uvm_reg_field ZQUpdate_ZQUpdate;
	rand uvm_reg_field ZQCalCodePUch0_ZQCalCodePUch0;
	rand uvm_reg_field ZQCalCodePDch0_ZQCalCodePDch0;
	rand uvm_reg_field ZQCalBaseCtrl_ZQCalBasePU;
	rand uvm_reg_field ZQCalBasePU;
	rand uvm_reg_field ZQCalBaseCtrl_ZQCalBasePD;
	rand uvm_reg_field ZQCalBasePD;
	rand uvm_reg_field ZQCalCodeOffsetPU_ZQCalCodeOffsetValPU;
	rand uvm_reg_field ZQCalCodeOffsetValPU;
	rand uvm_reg_field ZQCalCodeOffsetPD_ZQCalCodeOffsetValPD;
	rand uvm_reg_field ZQCalCodeOffsetValPD;
	rand uvm_reg_field ZQCalCodeOvrPU_ZQCalCodeOvrEnPU;
	rand uvm_reg_field ZQCalCodeOvrEnPU;
	rand uvm_reg_field ZQCalCodeOvrPU_ReservedZQCalCodeOvrEnPU;
	rand uvm_reg_field ReservedZQCalCodeOvrEnPU;
	rand uvm_reg_field ZQCalCodeOvrPU_ZQCalCodeOvrValPU;
	rand uvm_reg_field ZQCalCodeOvrValPU;
	rand uvm_reg_field ZQCalCodeOvrPD_ZQCalCodeOvrEnPD;
	rand uvm_reg_field ZQCalCodeOvrEnPD;
	rand uvm_reg_field ZQCalCodeOvrPD_ReservedZQCalCodeOvrEnPD;
	rand uvm_reg_field ReservedZQCalCodeOvrEnPD;
	rand uvm_reg_field ZQCalCodeOvrPD_ZQCalCodeOvrValPD;
	rand uvm_reg_field ZQCalCodeOvrValPD;
	rand uvm_reg_field ZQCalCodePUMax_ZQCalCodePUMax;
	rand uvm_reg_field ZQCalCodePUMin_ZQCalCodePUMin;
	rand uvm_reg_field ZQCalCodePDMax_ZQCalCodePDMax;
	rand uvm_reg_field ZQCalCodePDMin_ZQCalCodePDMin;
	rand uvm_reg_field ZQCalCodePUch1_ZQCalCodePUch1;
	rand uvm_reg_field ZQCalCodePDch1_ZQCalCodePDch1;
	rand uvm_reg_field ZCalStopClk_p0_ZCalStopClk_p0;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	ZcalClkDiv : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1 };
		option.weight = 1;
	}

	ZCalClkInfo_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4 };
		option.weight = 1;
	}

	MtestMuxSel : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1A };
		option.weight = 1;
	}

	ZCALParityInvert : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4D };
		option.weight = 1;
	}

	ScratchPadZCAL : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h7D };
		option.weight = 1;
	}

	ZCALReserved0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFC };
		option.weight = 1;
	}

	PUBReservedP1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFF };
		option.weight = 1;
	}

	ZCalBaseCtrl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h301 };
		option.weight = 1;
	}

	ZCalRate : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h303 };
		option.weight = 1;
	}

	ZCalCtrl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h305 };
		option.weight = 1;
	}

	ZCalCompInvert : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h306 };
		option.weight = 1;
	}

	ZCalCompOffset : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h307 };
		option.weight = 1;
	}

	ZCalPUOffset : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h308 };
		option.weight = 1;
	}

	ZCalCompOvr : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h309 };
		option.weight = 1;
	}

	ZCalPUOvr : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h30A };
		option.weight = 1;
	}

	ZCalClrFirstRunDone : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h30D };
		option.weight = 1;
	}

	ZCalPDSearchGainTV : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h30E };
		option.weight = 1;
	}

	ZCalAnaSettlingTime : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h30F };
		option.weight = 1;
	}

	ZCalReset : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h310 };
		option.weight = 1;
	}

	ZCalRun : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h311 };
		option.weight = 1;
	}

	ZCalBusy : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h312 };
		option.weight = 1;
	}

	ZCalCompResult : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h313 };
		option.weight = 1;
	}

	ZCalPUResult : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h314 };
		option.weight = 1;
	}

	ZCalPDResult : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h315 };
		option.weight = 1;
	}

	ZCalCodePU : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h316 };
		option.weight = 1;
	}

	ZCalCodePD : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h317 };
		option.weight = 1;
	}

	ZCalCompSearchSeed : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h318 };
		option.weight = 1;
	}

	ZCalPUSearchSeed : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h319 };
		option.weight = 1;
	}

	ZCalPDSearchSeed : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h31A };
		option.weight = 1;
	}

	ZCalCompSearchGainIV : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h31B };
		option.weight = 1;
	}

	ZCalCompSearchGainTV : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h31C };
		option.weight = 1;
	}

	ZCalPUSearchGainIV : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h31D };
		option.weight = 1;
	}

	ZCalPUSearchGainTV : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h31E };
		option.weight = 1;
	}

	ZCalPDSearchGainIV : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h31F };
		option.weight = 1;
	}

	ZQUpdate : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h320 };
		option.weight = 1;
	}

	ZQCalCodePUch0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h321 };
		option.weight = 1;
	}

	ZQCalCodePDch0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h322 };
		option.weight = 1;
	}

	ZQCalBaseCtrl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h323 };
		option.weight = 1;
	}

	ZQCalCodeOffsetPU : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h324 };
		option.weight = 1;
	}

	ZQCalCodeOffsetPD : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h325 };
		option.weight = 1;
	}

	ZQCalCodeOvrPU : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h326 };
		option.weight = 1;
	}

	ZQCalCodeOvrPD : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h327 };
		option.weight = 1;
	}

	ZQCalCodePUMax : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h328 };
		option.weight = 1;
	}

	ZQCalCodePUMin : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h329 };
		option.weight = 1;
	}

	ZQCalCodePDMax : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h32A };
		option.weight = 1;
	}

	ZQCalCodePDMin : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h32B };
		option.weight = 1;
	}

	ZQCalCodePUch1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h32D };
		option.weight = 1;
	}

	ZQCalCodePDch1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h32E };
		option.weight = 1;
	}

	ZCalStopClk_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h32F };
		option.weight = 1;
	}
endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p0");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.ZcalClkDiv = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZcalClkDiv::type_id::create("ZcalClkDiv",,get_full_name());
      if(this.ZcalClkDiv.has_coverage(UVM_CVR_ALL))
      	this.ZcalClkDiv.cg_bits.option.name = {get_name(), ".", "ZcalClkDiv_bits"};
      this.ZcalClkDiv.configure(this, null, "");
      this.ZcalClkDiv.build();
      this.default_map.add_reg(this.ZcalClkDiv, `UVM_REG_ADDR_WIDTH'h1, "RW", 0);
		this.ZcalClkDiv_ZcalClkDiv = this.ZcalClkDiv.ZcalClkDiv;
      this.ZCalClkInfo_p0 = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalClkInfo_p0::type_id::create("ZCalClkInfo_p0",,get_full_name());
      if(this.ZCalClkInfo_p0.has_coverage(UVM_CVR_ALL))
      	this.ZCalClkInfo_p0.cg_bits.option.name = {get_name(), ".", "ZCalClkInfo_p0_bits"};
      this.ZCalClkInfo_p0.configure(this, null, "");
      this.ZCalClkInfo_p0.build();
      this.default_map.add_reg(this.ZCalClkInfo_p0, `UVM_REG_ADDR_WIDTH'h4, "RW", 0);
		this.ZCalClkInfo_p0_ZCalDfiClkTicksPer1uS = this.ZCalClkInfo_p0.ZCalDfiClkTicksPer1uS;
		this.ZCalDfiClkTicksPer1uS = this.ZCalClkInfo_p0.ZCalDfiClkTicksPer1uS;
      this.MtestMuxSel = ral_reg_DWC_DDRPHYA_ZCAL0_p0_MtestMuxSel::type_id::create("MtestMuxSel",,get_full_name());
      if(this.MtestMuxSel.has_coverage(UVM_CVR_ALL))
      	this.MtestMuxSel.cg_bits.option.name = {get_name(), ".", "MtestMuxSel_bits"};
      this.MtestMuxSel.configure(this, null, "");
      this.MtestMuxSel.build();
      this.default_map.add_reg(this.MtestMuxSel, `UVM_REG_ADDR_WIDTH'h1A, "RW", 0);
		this.MtestMuxSel_MtestMuxSel = this.MtestMuxSel.MtestMuxSel;
      this.ZCALParityInvert = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCALParityInvert::type_id::create("ZCALParityInvert",,get_full_name());
      if(this.ZCALParityInvert.has_coverage(UVM_CVR_ALL))
      	this.ZCALParityInvert.cg_bits.option.name = {get_name(), ".", "ZCALParityInvert_bits"};
      this.ZCALParityInvert.configure(this, null, "");
      this.ZCALParityInvert.build();
      this.default_map.add_reg(this.ZCALParityInvert, `UVM_REG_ADDR_WIDTH'h4D, "RW", 0);
		this.ZCALParityInvert_ZCALParityInvert = this.ZCALParityInvert.ZCALParityInvert;
      this.ScratchPadZCAL = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ScratchPadZCAL::type_id::create("ScratchPadZCAL",,get_full_name());
      if(this.ScratchPadZCAL.has_coverage(UVM_CVR_ALL))
      	this.ScratchPadZCAL.cg_bits.option.name = {get_name(), ".", "ScratchPadZCAL_bits"};
      this.ScratchPadZCAL.configure(this, null, "");
      this.ScratchPadZCAL.build();
      this.default_map.add_reg(this.ScratchPadZCAL, `UVM_REG_ADDR_WIDTH'h7D, "RW", 0);
		this.ScratchPadZCAL_ScratchPadZCAL = this.ScratchPadZCAL.ScratchPadZCAL;
      this.ZCALReserved0 = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCALReserved0::type_id::create("ZCALReserved0",,get_full_name());
      if(this.ZCALReserved0.has_coverage(UVM_CVR_ALL))
      	this.ZCALReserved0.cg_bits.option.name = {get_name(), ".", "ZCALReserved0_bits"};
      this.ZCALReserved0.configure(this, null, "");
      this.ZCALReserved0.build();
      this.default_map.add_reg(this.ZCALReserved0, `UVM_REG_ADDR_WIDTH'hFC, "RW", 0);
		this.ZCALReserved0_ZCALReserved0 = this.ZCALReserved0.ZCALReserved0;
      this.PUBReservedP1_p0 = ral_reg_DWC_DDRPHYA_ZCAL0_p0_PUBReservedP1_p0::type_id::create("PUBReservedP1_p0",,get_full_name());
      if(this.PUBReservedP1_p0.has_coverage(UVM_CVR_ALL))
      	this.PUBReservedP1_p0.cg_bits.option.name = {get_name(), ".", "PUBReservedP1_p0_bits"};
      this.PUBReservedP1_p0.configure(this, null, "");
      this.PUBReservedP1_p0.build();
      this.default_map.add_reg(this.PUBReservedP1_p0, `UVM_REG_ADDR_WIDTH'hFF, "RW", 0);
		this.PUBReservedP1_p0_PUBReservedP1_p0 = this.PUBReservedP1_p0.PUBReservedP1_p0;
      this.ZCalBaseCtrl = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalBaseCtrl::type_id::create("ZCalBaseCtrl",,get_full_name());
      if(this.ZCalBaseCtrl.has_coverage(UVM_CVR_ALL))
      	this.ZCalBaseCtrl.cg_bits.option.name = {get_name(), ".", "ZCalBaseCtrl_bits"};
      this.ZCalBaseCtrl.configure(this, null, "");
      this.ZCalBaseCtrl.build();
      this.default_map.add_reg(this.ZCalBaseCtrl, `UVM_REG_ADDR_WIDTH'h301, "RW", 0);
		this.ZCalBaseCtrl_ZCalBasePU = this.ZCalBaseCtrl.ZCalBasePU;
		this.ZCalBasePU = this.ZCalBaseCtrl.ZCalBasePU;
		this.ZCalBaseCtrl_ZCalBasePD = this.ZCalBaseCtrl.ZCalBasePD;
		this.ZCalBasePD = this.ZCalBaseCtrl.ZCalBasePD;
		this.ZCalBaseCtrl_ReservedZCalBase = this.ZCalBaseCtrl.ReservedZCalBase;
		this.ReservedZCalBase = this.ZCalBaseCtrl.ReservedZCalBase;
		this.ZCalBaseCtrl_ZCalTxModeCtl = this.ZCalBaseCtrl.ZCalTxModeCtl;
		this.ZCalTxModeCtl = this.ZCalBaseCtrl.ZCalTxModeCtl;
		this.ZCalBaseCtrl_ReservedZCalTxModeCtl = this.ZCalBaseCtrl.ReservedZCalTxModeCtl;
		this.ReservedZCalTxModeCtl = this.ZCalBaseCtrl.ReservedZCalTxModeCtl;
		this.ZCalBaseCtrl_ZCalClkDis = this.ZCalBaseCtrl.ZCalClkDis;
		this.ZCalClkDis = this.ZCalBaseCtrl.ZCalClkDis;
      this.ZCalRate = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalRate::type_id::create("ZCalRate",,get_full_name());
      if(this.ZCalRate.has_coverage(UVM_CVR_ALL))
      	this.ZCalRate.cg_bits.option.name = {get_name(), ".", "ZCalRate_bits"};
      this.ZCalRate.configure(this, null, "");
      this.ZCalRate.build();
      this.default_map.add_reg(this.ZCalRate, `UVM_REG_ADDR_WIDTH'h303, "RW", 0);
		this.ZCalRate_ZCalInterval = this.ZCalRate.ZCalInterval;
		this.ZCalInterval = this.ZCalRate.ZCalInterval;
		this.ZCalRate_ZCalOnce = this.ZCalRate.ZCalOnce;
		this.ZCalOnce = this.ZCalRate.ZCalOnce;
      this.ZCalCtrl = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCtrl::type_id::create("ZCalCtrl",,get_full_name());
      if(this.ZCalCtrl.has_coverage(UVM_CVR_ALL))
      	this.ZCalCtrl.cg_bits.option.name = {get_name(), ".", "ZCalCtrl_bits"};
      this.ZCalCtrl.configure(this, null, "");
      this.ZCalCtrl.build();
      this.default_map.add_reg(this.ZCalCtrl, `UVM_REG_ADDR_WIDTH'h305, "RW", 0);
		this.ZCalCtrl_ReservedZCalCancelRoundErrDis = this.ZCalCtrl.ReservedZCalCancelRoundErrDis;
		this.ReservedZCalCancelRoundErrDis = this.ZCalCtrl.ReservedZCalCancelRoundErrDis;
		this.ZCalCtrl_ReservedZCalSlowComp = this.ZCalCtrl.ReservedZCalSlowComp;
		this.ReservedZCalSlowComp = this.ZCalCtrl.ReservedZCalSlowComp;
		this.ZCalCtrl_ZCalPURoundUp = this.ZCalCtrl.ZCalPURoundUp;
		this.ZCalPURoundUp = this.ZCalCtrl.ZCalPURoundUp;
		this.ZCalCtrl_ZCalPDRoundUp = this.ZCalCtrl.ZCalPDRoundUp;
		this.ZCalPDRoundUp = this.ZCalCtrl.ZCalPDRoundUp;
		this.ZCalCtrl_ZCalMaxTestsNumber = this.ZCalCtrl.ZCalMaxTestsNumber;
		this.ZCalMaxTestsNumber = this.ZCalCtrl.ZCalMaxTestsNumber;
		this.ZCalCtrl_ZCalDoubleLoopEn = this.ZCalCtrl.ZCalDoubleLoopEn;
		this.ZCalDoubleLoopEn = this.ZCalCtrl.ZCalDoubleLoopEn;
      this.ZCalCompInvert = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompInvert::type_id::create("ZCalCompInvert",,get_full_name());
      if(this.ZCalCompInvert.has_coverage(UVM_CVR_ALL))
      	this.ZCalCompInvert.cg_bits.option.name = {get_name(), ".", "ZCalCompInvert_bits"};
      this.ZCalCompInvert.configure(this, null, "");
      this.ZCalCompInvert.build();
      this.default_map.add_reg(this.ZCalCompInvert, `UVM_REG_ADDR_WIDTH'h306, "RW", 0);
		this.ZCalCompInvert_ZCalCompInvertComp = this.ZCalCompInvert.ZCalCompInvertComp;
		this.ZCalCompInvertComp = this.ZCalCompInvert.ZCalCompInvertComp;
		this.ZCalCompInvert_ZCalCompInvertPU = this.ZCalCompInvert.ZCalCompInvertPU;
		this.ZCalCompInvertPU = this.ZCalCompInvert.ZCalCompInvertPU;
		this.ZCalCompInvert_ZCalCompInvertPD = this.ZCalCompInvert.ZCalCompInvertPD;
		this.ZCalCompInvertPD = this.ZCalCompInvert.ZCalCompInvertPD;
      this.ZCalCompOffset = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompOffset::type_id::create("ZCalCompOffset",,get_full_name());
      if(this.ZCalCompOffset.has_coverage(UVM_CVR_ALL))
      	this.ZCalCompOffset.cg_bits.option.name = {get_name(), ".", "ZCalCompOffset_bits"};
      this.ZCalCompOffset.configure(this, null, "");
      this.ZCalCompOffset.build();
      this.default_map.add_reg(this.ZCalCompOffset, `UVM_REG_ADDR_WIDTH'h307, "RW", 0);
		this.ZCalCompOffset_ZCalCompOffsetVal = this.ZCalCompOffset.ZCalCompOffsetVal;
		this.ZCalCompOffsetVal = this.ZCalCompOffset.ZCalCompOffsetVal;
      this.ZCalPUOffset = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUOffset::type_id::create("ZCalPUOffset",,get_full_name());
      if(this.ZCalPUOffset.has_coverage(UVM_CVR_ALL))
      	this.ZCalPUOffset.cg_bits.option.name = {get_name(), ".", "ZCalPUOffset_bits"};
      this.ZCalPUOffset.configure(this, null, "");
      this.ZCalPUOffset.build();
      this.default_map.add_reg(this.ZCalPUOffset, `UVM_REG_ADDR_WIDTH'h308, "RW", 0);
		this.ZCalPUOffset_ZCalPUOffsetVal = this.ZCalPUOffset.ZCalPUOffsetVal;
		this.ZCalPUOffsetVal = this.ZCalPUOffset.ZCalPUOffsetVal;
      this.ZCalCompOvr = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompOvr::type_id::create("ZCalCompOvr",,get_full_name());
      if(this.ZCalCompOvr.has_coverage(UVM_CVR_ALL))
      	this.ZCalCompOvr.cg_bits.option.name = {get_name(), ".", "ZCalCompOvr_bits"};
      this.ZCalCompOvr.configure(this, null, "");
      this.ZCalCompOvr.build();
      this.default_map.add_reg(this.ZCalCompOvr, `UVM_REG_ADDR_WIDTH'h309, "RW", 0);
		this.ZCalCompOvr_ZCalCompOvrEn = this.ZCalCompOvr.ZCalCompOvrEn;
		this.ZCalCompOvrEn = this.ZCalCompOvr.ZCalCompOvrEn;
		this.ZCalCompOvr_ReservedZCalCompOvrEn = this.ZCalCompOvr.ReservedZCalCompOvrEn;
		this.ReservedZCalCompOvrEn = this.ZCalCompOvr.ReservedZCalCompOvrEn;
		this.ZCalCompOvr_ZCalCompOvrVal = this.ZCalCompOvr.ZCalCompOvrVal;
		this.ZCalCompOvrVal = this.ZCalCompOvr.ZCalCompOvrVal;
		this.ZCalCompOvr_ReservedZCalCompOvrVal = this.ZCalCompOvr.ReservedZCalCompOvrVal;
		this.ReservedZCalCompOvrVal = this.ZCalCompOvr.ReservedZCalCompOvrVal;
      this.ZCalPUOvr = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUOvr::type_id::create("ZCalPUOvr",,get_full_name());
      if(this.ZCalPUOvr.has_coverage(UVM_CVR_ALL))
      	this.ZCalPUOvr.cg_bits.option.name = {get_name(), ".", "ZCalPUOvr_bits"};
      this.ZCalPUOvr.configure(this, null, "");
      this.ZCalPUOvr.build();
      this.default_map.add_reg(this.ZCalPUOvr, `UVM_REG_ADDR_WIDTH'h30A, "RW", 0);
		this.ZCalPUOvr_ZCalPUOvrEn = this.ZCalPUOvr.ZCalPUOvrEn;
		this.ZCalPUOvrEn = this.ZCalPUOvr.ZCalPUOvrEn;
		this.ZCalPUOvr_ReservedZCalPUOvrEn = this.ZCalPUOvr.ReservedZCalPUOvrEn;
		this.ReservedZCalPUOvrEn = this.ZCalPUOvr.ReservedZCalPUOvrEn;
		this.ZCalPUOvr_ZCalPUOvrVal = this.ZCalPUOvr.ZCalPUOvrVal;
		this.ZCalPUOvrVal = this.ZCalPUOvr.ZCalPUOvrVal;
      this.ZCalClrFirstRunDone = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalClrFirstRunDone::type_id::create("ZCalClrFirstRunDone",,get_full_name());
      if(this.ZCalClrFirstRunDone.has_coverage(UVM_CVR_ALL))
      	this.ZCalClrFirstRunDone.cg_bits.option.name = {get_name(), ".", "ZCalClrFirstRunDone_bits"};
      this.ZCalClrFirstRunDone.configure(this, null, "");
      this.ZCalClrFirstRunDone.build();
      this.default_map.add_reg(this.ZCalClrFirstRunDone, `UVM_REG_ADDR_WIDTH'h30D, "RW", 0);
		this.ZCalClrFirstRunDone_ZCalClrFirstRunDone = this.ZCalClrFirstRunDone.ZCalClrFirstRunDone;
      this.ZCalPDSearchGainTV = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPDSearchGainTV::type_id::create("ZCalPDSearchGainTV",,get_full_name());
      if(this.ZCalPDSearchGainTV.has_coverage(UVM_CVR_ALL))
      	this.ZCalPDSearchGainTV.cg_bits.option.name = {get_name(), ".", "ZCalPDSearchGainTV_bits"};
      this.ZCalPDSearchGainTV.configure(this, null, "");
      this.ZCalPDSearchGainTV.build();
      this.default_map.add_reg(this.ZCalPDSearchGainTV, `UVM_REG_ADDR_WIDTH'h30E, "RW", 0);
		this.ZCalPDSearchGainTV_ZCalPDSearchGainTVVal = this.ZCalPDSearchGainTV.ZCalPDSearchGainTVVal;
		this.ZCalPDSearchGainTVVal = this.ZCalPDSearchGainTV.ZCalPDSearchGainTVVal;
		this.ZCalPDSearchGainTV_ZCalPDSearchGainTVValB = this.ZCalPDSearchGainTV.ZCalPDSearchGainTVValB;
		this.ZCalPDSearchGainTVValB = this.ZCalPDSearchGainTV.ZCalPDSearchGainTVValB;
		this.ZCalPDSearchGainTV_ZCalPDSearchGainTVAuto = this.ZCalPDSearchGainTV.ZCalPDSearchGainTVAuto;
		this.ZCalPDSearchGainTVAuto = this.ZCalPDSearchGainTV.ZCalPDSearchGainTVAuto;
      this.ZCalAnaSettlingTime = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalAnaSettlingTime::type_id::create("ZCalAnaSettlingTime",,get_full_name());
      if(this.ZCalAnaSettlingTime.has_coverage(UVM_CVR_ALL))
      	this.ZCalAnaSettlingTime.cg_bits.option.name = {get_name(), ".", "ZCalAnaSettlingTime_bits"};
      this.ZCalAnaSettlingTime.configure(this, null, "");
      this.ZCalAnaSettlingTime.build();
      this.default_map.add_reg(this.ZCalAnaSettlingTime, `UVM_REG_ADDR_WIDTH'h30F, "RW", 0);
		this.ZCalAnaSettlingTime_ZCalAnaSettlingTime = this.ZCalAnaSettlingTime.ZCalAnaSettlingTime;
      this.ZCalReset = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalReset::type_id::create("ZCalReset",,get_full_name());
      if(this.ZCalReset.has_coverage(UVM_CVR_ALL))
      	this.ZCalReset.cg_bits.option.name = {get_name(), ".", "ZCalReset_bits"};
      this.ZCalReset.configure(this, null, "");
      this.ZCalReset.build();
      this.default_map.add_reg(this.ZCalReset, `UVM_REG_ADDR_WIDTH'h310, "RW", 0);
		this.ZCalReset_ZCalReset = this.ZCalReset.ZCalReset;
      this.ZCalRun = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalRun::type_id::create("ZCalRun",,get_full_name());
      if(this.ZCalRun.has_coverage(UVM_CVR_ALL))
      	this.ZCalRun.cg_bits.option.name = {get_name(), ".", "ZCalRun_bits"};
      this.ZCalRun.configure(this, null, "");
      this.ZCalRun.build();
      this.default_map.add_reg(this.ZCalRun, `UVM_REG_ADDR_WIDTH'h311, "RW", 0);
		this.ZCalRun_ZCalRun = this.ZCalRun.ZCalRun;
      this.ZCalBusy = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalBusy::type_id::create("ZCalBusy",,get_full_name());
      if(this.ZCalBusy.has_coverage(UVM_CVR_ALL))
      	this.ZCalBusy.cg_bits.option.name = {get_name(), ".", "ZCalBusy_bits"};
      this.ZCalBusy.configure(this, null, "");
      this.ZCalBusy.build();
      this.default_map.add_reg(this.ZCalBusy, `UVM_REG_ADDR_WIDTH'h312, "RO", 0);
		this.ZCalBusy_ZCalBusy = this.ZCalBusy.ZCalBusy;
      this.ZCalCompResult = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompResult::type_id::create("ZCalCompResult",,get_full_name());
      if(this.ZCalCompResult.has_coverage(UVM_CVR_ALL))
      	this.ZCalCompResult.cg_bits.option.name = {get_name(), ".", "ZCalCompResult_bits"};
      this.ZCalCompResult.configure(this, null, "");
      this.ZCalCompResult.build();
      this.default_map.add_reg(this.ZCalCompResult, `UVM_REG_ADDR_WIDTH'h313, "RO", 0);
		this.ZCalCompResult_ZCalCompResult = this.ZCalCompResult.ZCalCompResult;
      this.ZCalPUResult = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUResult::type_id::create("ZCalPUResult",,get_full_name());
      if(this.ZCalPUResult.has_coverage(UVM_CVR_ALL))
      	this.ZCalPUResult.cg_bits.option.name = {get_name(), ".", "ZCalPUResult_bits"};
      this.ZCalPUResult.configure(this, null, "");
      this.ZCalPUResult.build();
      this.default_map.add_reg(this.ZCalPUResult, `UVM_REG_ADDR_WIDTH'h314, "RO", 0);
		this.ZCalPUResult_ZCalPUResult = this.ZCalPUResult.ZCalPUResult;
      this.ZCalPDResult = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPDResult::type_id::create("ZCalPDResult",,get_full_name());
      if(this.ZCalPDResult.has_coverage(UVM_CVR_ALL))
      	this.ZCalPDResult.cg_bits.option.name = {get_name(), ".", "ZCalPDResult_bits"};
      this.ZCalPDResult.configure(this, null, "");
      this.ZCalPDResult.build();
      this.default_map.add_reg(this.ZCalPDResult, `UVM_REG_ADDR_WIDTH'h315, "RO", 0);
		this.ZCalPDResult_ZCalPDResult = this.ZCalPDResult.ZCalPDResult;
      this.ZCalCodePU = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCodePU::type_id::create("ZCalCodePU",,get_full_name());
      if(this.ZCalCodePU.has_coverage(UVM_CVR_ALL))
      	this.ZCalCodePU.cg_bits.option.name = {get_name(), ".", "ZCalCodePU_bits"};
      this.ZCalCodePU.configure(this, null, "");
      this.ZCalCodePU.build();
      this.default_map.add_reg(this.ZCalCodePU, `UVM_REG_ADDR_WIDTH'h316, "RO", 0);
		this.ZCalCodePU_ZCalCodePU = this.ZCalCodePU.ZCalCodePU;
      this.ZCalCodePD = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCodePD::type_id::create("ZCalCodePD",,get_full_name());
      if(this.ZCalCodePD.has_coverage(UVM_CVR_ALL))
      	this.ZCalCodePD.cg_bits.option.name = {get_name(), ".", "ZCalCodePD_bits"};
      this.ZCalCodePD.configure(this, null, "");
      this.ZCalCodePD.build();
      this.default_map.add_reg(this.ZCalCodePD, `UVM_REG_ADDR_WIDTH'h317, "RO", 0);
		this.ZCalCodePD_ZCalCodePD = this.ZCalCodePD.ZCalCodePD;
      this.ZCalCompSearchSeed = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompSearchSeed::type_id::create("ZCalCompSearchSeed",,get_full_name());
      if(this.ZCalCompSearchSeed.has_coverage(UVM_CVR_ALL))
      	this.ZCalCompSearchSeed.cg_bits.option.name = {get_name(), ".", "ZCalCompSearchSeed_bits"};
      this.ZCalCompSearchSeed.configure(this, null, "");
      this.ZCalCompSearchSeed.build();
      this.default_map.add_reg(this.ZCalCompSearchSeed, `UVM_REG_ADDR_WIDTH'h318, "RW", 0);
		this.ZCalCompSearchSeed_ZCalCompSearchSeedVal = this.ZCalCompSearchSeed.ZCalCompSearchSeedVal;
		this.ZCalCompSearchSeedVal = this.ZCalCompSearchSeed.ZCalCompSearchSeedVal;
		this.ZCalCompSearchSeed_ReservedZCalCompSearchSeedVal = this.ZCalCompSearchSeed.ReservedZCalCompSearchSeedVal;
		this.ReservedZCalCompSearchSeedVal = this.ZCalCompSearchSeed.ReservedZCalCompSearchSeedVal;
		this.ZCalCompSearchSeed_ZCalCompSearchSeedAuto = this.ZCalCompSearchSeed.ZCalCompSearchSeedAuto;
		this.ZCalCompSearchSeedAuto = this.ZCalCompSearchSeed.ZCalCompSearchSeedAuto;
      this.ZCalPUSearchSeed = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUSearchSeed::type_id::create("ZCalPUSearchSeed",,get_full_name());
      if(this.ZCalPUSearchSeed.has_coverage(UVM_CVR_ALL))
      	this.ZCalPUSearchSeed.cg_bits.option.name = {get_name(), ".", "ZCalPUSearchSeed_bits"};
      this.ZCalPUSearchSeed.configure(this, null, "");
      this.ZCalPUSearchSeed.build();
      this.default_map.add_reg(this.ZCalPUSearchSeed, `UVM_REG_ADDR_WIDTH'h319, "RW", 0);
		this.ZCalPUSearchSeed_ZCalPUSearchSeedVal = this.ZCalPUSearchSeed.ZCalPUSearchSeedVal;
		this.ZCalPUSearchSeedVal = this.ZCalPUSearchSeed.ZCalPUSearchSeedVal;
		this.ZCalPUSearchSeed_ZCalPUSearchSeedAuto = this.ZCalPUSearchSeed.ZCalPUSearchSeedAuto;
		this.ZCalPUSearchSeedAuto = this.ZCalPUSearchSeed.ZCalPUSearchSeedAuto;
      this.ZCalPDSearchSeed = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPDSearchSeed::type_id::create("ZCalPDSearchSeed",,get_full_name());
      if(this.ZCalPDSearchSeed.has_coverage(UVM_CVR_ALL))
      	this.ZCalPDSearchSeed.cg_bits.option.name = {get_name(), ".", "ZCalPDSearchSeed_bits"};
      this.ZCalPDSearchSeed.configure(this, null, "");
      this.ZCalPDSearchSeed.build();
      this.default_map.add_reg(this.ZCalPDSearchSeed, `UVM_REG_ADDR_WIDTH'h31A, "RW", 0);
		this.ZCalPDSearchSeed_ZCalPDSearchSeedVal = this.ZCalPDSearchSeed.ZCalPDSearchSeedVal;
		this.ZCalPDSearchSeedVal = this.ZCalPDSearchSeed.ZCalPDSearchSeedVal;
		this.ZCalPDSearchSeed_ZCalPDSearchSeedAuto = this.ZCalPDSearchSeed.ZCalPDSearchSeedAuto;
		this.ZCalPDSearchSeedAuto = this.ZCalPDSearchSeed.ZCalPDSearchSeedAuto;
      this.ZCalCompSearchGainIV = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompSearchGainIV::type_id::create("ZCalCompSearchGainIV",,get_full_name());
      if(this.ZCalCompSearchGainIV.has_coverage(UVM_CVR_ALL))
      	this.ZCalCompSearchGainIV.cg_bits.option.name = {get_name(), ".", "ZCalCompSearchGainIV_bits"};
      this.ZCalCompSearchGainIV.configure(this, null, "");
      this.ZCalCompSearchGainIV.build();
      this.default_map.add_reg(this.ZCalCompSearchGainIV, `UVM_REG_ADDR_WIDTH'h31B, "RW", 0);
		this.ZCalCompSearchGainIV_ZCalCompSearchGainIVVal = this.ZCalCompSearchGainIV.ZCalCompSearchGainIVVal;
		this.ZCalCompSearchGainIVVal = this.ZCalCompSearchGainIV.ZCalCompSearchGainIVVal;
		this.ZCalCompSearchGainIV_ZCalCompSearchGainIVValB = this.ZCalCompSearchGainIV.ZCalCompSearchGainIVValB;
		this.ZCalCompSearchGainIVValB = this.ZCalCompSearchGainIV.ZCalCompSearchGainIVValB;
		this.ZCalCompSearchGainIV_ZCalCompSearchGainIVAuto = this.ZCalCompSearchGainIV.ZCalCompSearchGainIVAuto;
		this.ZCalCompSearchGainIVAuto = this.ZCalCompSearchGainIV.ZCalCompSearchGainIVAuto;
      this.ZCalCompSearchGainTV = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalCompSearchGainTV::type_id::create("ZCalCompSearchGainTV",,get_full_name());
      if(this.ZCalCompSearchGainTV.has_coverage(UVM_CVR_ALL))
      	this.ZCalCompSearchGainTV.cg_bits.option.name = {get_name(), ".", "ZCalCompSearchGainTV_bits"};
      this.ZCalCompSearchGainTV.configure(this, null, "");
      this.ZCalCompSearchGainTV.build();
      this.default_map.add_reg(this.ZCalCompSearchGainTV, `UVM_REG_ADDR_WIDTH'h31C, "RW", 0);
		this.ZCalCompSearchGainTV_ZCalCompSearchGainTVVal = this.ZCalCompSearchGainTV.ZCalCompSearchGainTVVal;
		this.ZCalCompSearchGainTVVal = this.ZCalCompSearchGainTV.ZCalCompSearchGainTVVal;
		this.ZCalCompSearchGainTV_ZCalCompSearchGainTVValB = this.ZCalCompSearchGainTV.ZCalCompSearchGainTVValB;
		this.ZCalCompSearchGainTVValB = this.ZCalCompSearchGainTV.ZCalCompSearchGainTVValB;
		this.ZCalCompSearchGainTV_ZCalCompSearchGainTVAuto = this.ZCalCompSearchGainTV.ZCalCompSearchGainTVAuto;
		this.ZCalCompSearchGainTVAuto = this.ZCalCompSearchGainTV.ZCalCompSearchGainTVAuto;
      this.ZCalPUSearchGainIV = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUSearchGainIV::type_id::create("ZCalPUSearchGainIV",,get_full_name());
      if(this.ZCalPUSearchGainIV.has_coverage(UVM_CVR_ALL))
      	this.ZCalPUSearchGainIV.cg_bits.option.name = {get_name(), ".", "ZCalPUSearchGainIV_bits"};
      this.ZCalPUSearchGainIV.configure(this, null, "");
      this.ZCalPUSearchGainIV.build();
      this.default_map.add_reg(this.ZCalPUSearchGainIV, `UVM_REG_ADDR_WIDTH'h31D, "RW", 0);
		this.ZCalPUSearchGainIV_ZCalPUSearchGainIVVal = this.ZCalPUSearchGainIV.ZCalPUSearchGainIVVal;
		this.ZCalPUSearchGainIVVal = this.ZCalPUSearchGainIV.ZCalPUSearchGainIVVal;
		this.ZCalPUSearchGainIV_ZCalPUSearchGainIVValB = this.ZCalPUSearchGainIV.ZCalPUSearchGainIVValB;
		this.ZCalPUSearchGainIVValB = this.ZCalPUSearchGainIV.ZCalPUSearchGainIVValB;
		this.ZCalPUSearchGainIV_ZCalPUSearchGainIVAuto = this.ZCalPUSearchGainIV.ZCalPUSearchGainIVAuto;
		this.ZCalPUSearchGainIVAuto = this.ZCalPUSearchGainIV.ZCalPUSearchGainIVAuto;
      this.ZCalPUSearchGainTV = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPUSearchGainTV::type_id::create("ZCalPUSearchGainTV",,get_full_name());
      if(this.ZCalPUSearchGainTV.has_coverage(UVM_CVR_ALL))
      	this.ZCalPUSearchGainTV.cg_bits.option.name = {get_name(), ".", "ZCalPUSearchGainTV_bits"};
      this.ZCalPUSearchGainTV.configure(this, null, "");
      this.ZCalPUSearchGainTV.build();
      this.default_map.add_reg(this.ZCalPUSearchGainTV, `UVM_REG_ADDR_WIDTH'h31E, "RW", 0);
		this.ZCalPUSearchGainTV_ZCalPUSearchGainTVVal = this.ZCalPUSearchGainTV.ZCalPUSearchGainTVVal;
		this.ZCalPUSearchGainTVVal = this.ZCalPUSearchGainTV.ZCalPUSearchGainTVVal;
		this.ZCalPUSearchGainTV_ZCalPUSearchGainTVValB = this.ZCalPUSearchGainTV.ZCalPUSearchGainTVValB;
		this.ZCalPUSearchGainTVValB = this.ZCalPUSearchGainTV.ZCalPUSearchGainTVValB;
		this.ZCalPUSearchGainTV_ZCalPUSearchGainTVAuto = this.ZCalPUSearchGainTV.ZCalPUSearchGainTVAuto;
		this.ZCalPUSearchGainTVAuto = this.ZCalPUSearchGainTV.ZCalPUSearchGainTVAuto;
      this.ZCalPDSearchGainIV = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalPDSearchGainIV::type_id::create("ZCalPDSearchGainIV",,get_full_name());
      if(this.ZCalPDSearchGainIV.has_coverage(UVM_CVR_ALL))
      	this.ZCalPDSearchGainIV.cg_bits.option.name = {get_name(), ".", "ZCalPDSearchGainIV_bits"};
      this.ZCalPDSearchGainIV.configure(this, null, "");
      this.ZCalPDSearchGainIV.build();
      this.default_map.add_reg(this.ZCalPDSearchGainIV, `UVM_REG_ADDR_WIDTH'h31F, "RW", 0);
		this.ZCalPDSearchGainIV_ZCalPDSearchGainIVVal = this.ZCalPDSearchGainIV.ZCalPDSearchGainIVVal;
		this.ZCalPDSearchGainIVVal = this.ZCalPDSearchGainIV.ZCalPDSearchGainIVVal;
		this.ZCalPDSearchGainIV_ZCalPDSearchGainIVValB = this.ZCalPDSearchGainIV.ZCalPDSearchGainIVValB;
		this.ZCalPDSearchGainIVValB = this.ZCalPDSearchGainIV.ZCalPDSearchGainIVValB;
		this.ZCalPDSearchGainIV_ZCalPDSearchGainIVAuto = this.ZCalPDSearchGainIV.ZCalPDSearchGainIVAuto;
		this.ZCalPDSearchGainIVAuto = this.ZCalPDSearchGainIV.ZCalPDSearchGainIVAuto;
      this.ZQUpdate = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQUpdate::type_id::create("ZQUpdate",,get_full_name());
      if(this.ZQUpdate.has_coverage(UVM_CVR_ALL))
      	this.ZQUpdate.cg_bits.option.name = {get_name(), ".", "ZQUpdate_bits"};
      this.ZQUpdate.configure(this, null, "");
      this.ZQUpdate.build();
      this.default_map.add_reg(this.ZQUpdate, `UVM_REG_ADDR_WIDTH'h320, "RW", 0);
		this.ZQUpdate_ZQUpdate = this.ZQUpdate.ZQUpdate;
      this.ZQCalCodePUch0 = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUch0::type_id::create("ZQCalCodePUch0",,get_full_name());
      if(this.ZQCalCodePUch0.has_coverage(UVM_CVR_ALL))
      	this.ZQCalCodePUch0.cg_bits.option.name = {get_name(), ".", "ZQCalCodePUch0_bits"};
      this.ZQCalCodePUch0.configure(this, null, "");
      this.ZQCalCodePUch0.build();
      this.default_map.add_reg(this.ZQCalCodePUch0, `UVM_REG_ADDR_WIDTH'h321, "RW", 0);
		this.ZQCalCodePUch0_ZQCalCodePUch0 = this.ZQCalCodePUch0.ZQCalCodePUch0;
      this.ZQCalCodePDch0 = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDch0::type_id::create("ZQCalCodePDch0",,get_full_name());
      if(this.ZQCalCodePDch0.has_coverage(UVM_CVR_ALL))
      	this.ZQCalCodePDch0.cg_bits.option.name = {get_name(), ".", "ZQCalCodePDch0_bits"};
      this.ZQCalCodePDch0.configure(this, null, "");
      this.ZQCalCodePDch0.build();
      this.default_map.add_reg(this.ZQCalCodePDch0, `UVM_REG_ADDR_WIDTH'h322, "RW", 0);
		this.ZQCalCodePDch0_ZQCalCodePDch0 = this.ZQCalCodePDch0.ZQCalCodePDch0;
      this.ZQCalBaseCtrl = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalBaseCtrl::type_id::create("ZQCalBaseCtrl",,get_full_name());
      if(this.ZQCalBaseCtrl.has_coverage(UVM_CVR_ALL))
      	this.ZQCalBaseCtrl.cg_bits.option.name = {get_name(), ".", "ZQCalBaseCtrl_bits"};
      this.ZQCalBaseCtrl.configure(this, null, "");
      this.ZQCalBaseCtrl.build();
      this.default_map.add_reg(this.ZQCalBaseCtrl, `UVM_REG_ADDR_WIDTH'h323, "RW", 0);
		this.ZQCalBaseCtrl_ZQCalBasePU = this.ZQCalBaseCtrl.ZQCalBasePU;
		this.ZQCalBasePU = this.ZQCalBaseCtrl.ZQCalBasePU;
		this.ZQCalBaseCtrl_ZQCalBasePD = this.ZQCalBaseCtrl.ZQCalBasePD;
		this.ZQCalBasePD = this.ZQCalBaseCtrl.ZQCalBasePD;
      this.ZQCalCodeOffsetPU = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOffsetPU::type_id::create("ZQCalCodeOffsetPU",,get_full_name());
      if(this.ZQCalCodeOffsetPU.has_coverage(UVM_CVR_ALL))
      	this.ZQCalCodeOffsetPU.cg_bits.option.name = {get_name(), ".", "ZQCalCodeOffsetPU_bits"};
      this.ZQCalCodeOffsetPU.configure(this, null, "");
      this.ZQCalCodeOffsetPU.build();
      this.default_map.add_reg(this.ZQCalCodeOffsetPU, `UVM_REG_ADDR_WIDTH'h324, "RW", 0);
		this.ZQCalCodeOffsetPU_ZQCalCodeOffsetValPU = this.ZQCalCodeOffsetPU.ZQCalCodeOffsetValPU;
		this.ZQCalCodeOffsetValPU = this.ZQCalCodeOffsetPU.ZQCalCodeOffsetValPU;
      this.ZQCalCodeOffsetPD = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOffsetPD::type_id::create("ZQCalCodeOffsetPD",,get_full_name());
      if(this.ZQCalCodeOffsetPD.has_coverage(UVM_CVR_ALL))
      	this.ZQCalCodeOffsetPD.cg_bits.option.name = {get_name(), ".", "ZQCalCodeOffsetPD_bits"};
      this.ZQCalCodeOffsetPD.configure(this, null, "");
      this.ZQCalCodeOffsetPD.build();
      this.default_map.add_reg(this.ZQCalCodeOffsetPD, `UVM_REG_ADDR_WIDTH'h325, "RW", 0);
		this.ZQCalCodeOffsetPD_ZQCalCodeOffsetValPD = this.ZQCalCodeOffsetPD.ZQCalCodeOffsetValPD;
		this.ZQCalCodeOffsetValPD = this.ZQCalCodeOffsetPD.ZQCalCodeOffsetValPD;
      this.ZQCalCodeOvrPU = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOvrPU::type_id::create("ZQCalCodeOvrPU",,get_full_name());
      if(this.ZQCalCodeOvrPU.has_coverage(UVM_CVR_ALL))
      	this.ZQCalCodeOvrPU.cg_bits.option.name = {get_name(), ".", "ZQCalCodeOvrPU_bits"};
      this.ZQCalCodeOvrPU.configure(this, null, "");
      this.ZQCalCodeOvrPU.build();
      this.default_map.add_reg(this.ZQCalCodeOvrPU, `UVM_REG_ADDR_WIDTH'h326, "RW", 0);
		this.ZQCalCodeOvrPU_ZQCalCodeOvrEnPU = this.ZQCalCodeOvrPU.ZQCalCodeOvrEnPU;
		this.ZQCalCodeOvrEnPU = this.ZQCalCodeOvrPU.ZQCalCodeOvrEnPU;
		this.ZQCalCodeOvrPU_ReservedZQCalCodeOvrEnPU = this.ZQCalCodeOvrPU.ReservedZQCalCodeOvrEnPU;
		this.ReservedZQCalCodeOvrEnPU = this.ZQCalCodeOvrPU.ReservedZQCalCodeOvrEnPU;
		this.ZQCalCodeOvrPU_ZQCalCodeOvrValPU = this.ZQCalCodeOvrPU.ZQCalCodeOvrValPU;
		this.ZQCalCodeOvrValPU = this.ZQCalCodeOvrPU.ZQCalCodeOvrValPU;
      this.ZQCalCodeOvrPD = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodeOvrPD::type_id::create("ZQCalCodeOvrPD",,get_full_name());
      if(this.ZQCalCodeOvrPD.has_coverage(UVM_CVR_ALL))
      	this.ZQCalCodeOvrPD.cg_bits.option.name = {get_name(), ".", "ZQCalCodeOvrPD_bits"};
      this.ZQCalCodeOvrPD.configure(this, null, "");
      this.ZQCalCodeOvrPD.build();
      this.default_map.add_reg(this.ZQCalCodeOvrPD, `UVM_REG_ADDR_WIDTH'h327, "RW", 0);
		this.ZQCalCodeOvrPD_ZQCalCodeOvrEnPD = this.ZQCalCodeOvrPD.ZQCalCodeOvrEnPD;
		this.ZQCalCodeOvrEnPD = this.ZQCalCodeOvrPD.ZQCalCodeOvrEnPD;
		this.ZQCalCodeOvrPD_ReservedZQCalCodeOvrEnPD = this.ZQCalCodeOvrPD.ReservedZQCalCodeOvrEnPD;
		this.ReservedZQCalCodeOvrEnPD = this.ZQCalCodeOvrPD.ReservedZQCalCodeOvrEnPD;
		this.ZQCalCodeOvrPD_ZQCalCodeOvrValPD = this.ZQCalCodeOvrPD.ZQCalCodeOvrValPD;
		this.ZQCalCodeOvrValPD = this.ZQCalCodeOvrPD.ZQCalCodeOvrValPD;
      this.ZQCalCodePUMax = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUMax::type_id::create("ZQCalCodePUMax",,get_full_name());
      if(this.ZQCalCodePUMax.has_coverage(UVM_CVR_ALL))
      	this.ZQCalCodePUMax.cg_bits.option.name = {get_name(), ".", "ZQCalCodePUMax_bits"};
      this.ZQCalCodePUMax.configure(this, null, "");
      this.ZQCalCodePUMax.build();
      this.default_map.add_reg(this.ZQCalCodePUMax, `UVM_REG_ADDR_WIDTH'h328, "RW", 0);
		this.ZQCalCodePUMax_ZQCalCodePUMax = this.ZQCalCodePUMax.ZQCalCodePUMax;
      this.ZQCalCodePUMin = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUMin::type_id::create("ZQCalCodePUMin",,get_full_name());
      if(this.ZQCalCodePUMin.has_coverage(UVM_CVR_ALL))
      	this.ZQCalCodePUMin.cg_bits.option.name = {get_name(), ".", "ZQCalCodePUMin_bits"};
      this.ZQCalCodePUMin.configure(this, null, "");
      this.ZQCalCodePUMin.build();
      this.default_map.add_reg(this.ZQCalCodePUMin, `UVM_REG_ADDR_WIDTH'h329, "RW", 0);
		this.ZQCalCodePUMin_ZQCalCodePUMin = this.ZQCalCodePUMin.ZQCalCodePUMin;
      this.ZQCalCodePDMax = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDMax::type_id::create("ZQCalCodePDMax",,get_full_name());
      if(this.ZQCalCodePDMax.has_coverage(UVM_CVR_ALL))
      	this.ZQCalCodePDMax.cg_bits.option.name = {get_name(), ".", "ZQCalCodePDMax_bits"};
      this.ZQCalCodePDMax.configure(this, null, "");
      this.ZQCalCodePDMax.build();
      this.default_map.add_reg(this.ZQCalCodePDMax, `UVM_REG_ADDR_WIDTH'h32A, "RW", 0);
		this.ZQCalCodePDMax_ZQCalCodePDMax = this.ZQCalCodePDMax.ZQCalCodePDMax;
      this.ZQCalCodePDMin = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDMin::type_id::create("ZQCalCodePDMin",,get_full_name());
      if(this.ZQCalCodePDMin.has_coverage(UVM_CVR_ALL))
      	this.ZQCalCodePDMin.cg_bits.option.name = {get_name(), ".", "ZQCalCodePDMin_bits"};
      this.ZQCalCodePDMin.configure(this, null, "");
      this.ZQCalCodePDMin.build();
      this.default_map.add_reg(this.ZQCalCodePDMin, `UVM_REG_ADDR_WIDTH'h32B, "RW", 0);
		this.ZQCalCodePDMin_ZQCalCodePDMin = this.ZQCalCodePDMin.ZQCalCodePDMin;
      this.ZQCalCodePUch1 = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePUch1::type_id::create("ZQCalCodePUch1",,get_full_name());
      if(this.ZQCalCodePUch1.has_coverage(UVM_CVR_ALL))
      	this.ZQCalCodePUch1.cg_bits.option.name = {get_name(), ".", "ZQCalCodePUch1_bits"};
      this.ZQCalCodePUch1.configure(this, null, "");
      this.ZQCalCodePUch1.build();
      this.default_map.add_reg(this.ZQCalCodePUch1, `UVM_REG_ADDR_WIDTH'h32D, "RW", 0);
		this.ZQCalCodePUch1_ZQCalCodePUch1 = this.ZQCalCodePUch1.ZQCalCodePUch1;
      this.ZQCalCodePDch1 = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZQCalCodePDch1::type_id::create("ZQCalCodePDch1",,get_full_name());
      if(this.ZQCalCodePDch1.has_coverage(UVM_CVR_ALL))
      	this.ZQCalCodePDch1.cg_bits.option.name = {get_name(), ".", "ZQCalCodePDch1_bits"};
      this.ZQCalCodePDch1.configure(this, null, "");
      this.ZQCalCodePDch1.build();
      this.default_map.add_reg(this.ZQCalCodePDch1, `UVM_REG_ADDR_WIDTH'h32E, "RW", 0);
		this.ZQCalCodePDch1_ZQCalCodePDch1 = this.ZQCalCodePDch1.ZQCalCodePDch1;
      this.ZCalStopClk_p0 = ral_reg_DWC_DDRPHYA_ZCAL0_p0_ZCalStopClk_p0::type_id::create("ZCalStopClk_p0",,get_full_name());
      if(this.ZCalStopClk_p0.has_coverage(UVM_CVR_ALL))
      	this.ZCalStopClk_p0.cg_bits.option.name = {get_name(), ".", "ZCalStopClk_p0_bits"};
      this.ZCalStopClk_p0.configure(this, null, "");
      this.ZCalStopClk_p0.build();
      this.default_map.add_reg(this.ZCalStopClk_p0, `UVM_REG_ADDR_WIDTH'h32F, "RW", 0);
		this.ZCalStopClk_p0_ZCalStopClk_p0 = this.ZCalStopClk_p0.ZCalStopClk_p0;
   endfunction : build

	`uvm_object_utils(ral_block_DWC_DDRPHYA_ZCAL0_p0)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_DDRPHYA_ZCAL0_p0


endpackage
`endif
