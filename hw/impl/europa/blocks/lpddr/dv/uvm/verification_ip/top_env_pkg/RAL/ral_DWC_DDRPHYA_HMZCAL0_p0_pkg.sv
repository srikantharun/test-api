`ifndef RAL_DWC_DDRPHYA_HMZCAL0_P0_PKG
`define RAL_DWC_DDRPHYA_HMZCAL0_P0_PKG

package ral_DWC_DDRPHYA_HMZCAL0_p0_pkg;
import uvm_pkg::*;

class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZcalPowerCtl extends uvm_reg;
	rand uvm_reg_field RxPowerDown;
	rand uvm_reg_field RxStandby;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxPowerDown: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   RxStandby: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_ZcalPowerCtl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxPowerDown = uvm_reg_field::type_id::create("RxPowerDown",,get_full_name());
      this.RxPowerDown.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 0);
      this.RxStandby = uvm_reg_field::type_id::create("RxStandby",,get_full_name());
      this.RxStandby.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZcalPowerCtl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZcalPowerCtl


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxCurrAdj extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_RxCurrAdj");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxCurrAdj = uvm_reg_field::type_id::create("RxCurrAdj",,get_full_name());
      this.RxCurrAdj.configure(this, 8, 0, "RW", 0, 8'h9, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxCurrAdj)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxCurrAdj


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxDfeModeCfg_p0 extends uvm_reg;
	rand uvm_reg_field RxDfeCtrl;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDfeCtrl: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_RxDfeModeCfg_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDfeCtrl = uvm_reg_field::type_id::create("RxDfeCtrl",,get_full_name());
      this.RxDfeCtrl.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxDfeModeCfg_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxDfeModeCfg_p0


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxModeCtl extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_RxModeCtl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxModeCtl = uvm_reg_field::type_id::create("RxModeCtl",,get_full_name());
      this.RxModeCtl.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxModeCtl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxModeCtl


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxMiscCtl extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_RxMiscCtl");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxMiscCtl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxMiscCtl


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_MtestMuxSel extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_MtestMuxSel");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MtestMuxSel = uvm_reg_field::type_id::create("MtestMuxSel",,get_full_name());
      this.MtestMuxSel.configure(this, 10, 0, "RW", 0, 10'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_MtestMuxSel)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_MtestMuxSel


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_HMZCALParityInvert extends uvm_reg;
	rand uvm_reg_field HMZCALParityInvert;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HMZCALParityInvert: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_HMZCALParityInvert");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMZCALParityInvert = uvm_reg_field::type_id::create("HMZCALParityInvert",,get_full_name());
      this.HMZCALParityInvert.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_HMZCALParityInvert)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_HMZCALParityInvert


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ScratchPadHMZCAL extends uvm_reg;
	rand uvm_reg_field ScratchPadHMZCAL;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ScratchPadHMZCAL: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_ScratchPadHMZCAL");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ScratchPadHMZCAL = uvm_reg_field::type_id::create("ScratchPadHMZCAL",,get_full_name());
      this.ScratchPadHMZCAL.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ScratchPadHMZCAL)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ScratchPadHMZCAL


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_HardMacroModeSel extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_HardMacroModeSel");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HardMacroModeSel = uvm_reg_field::type_id::create("HardMacroModeSel",,get_full_name());
      this.HardMacroModeSel.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_HardMacroModeSel)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_HardMacroModeSel


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_TxFuncMode extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_TxFuncMode");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxFuncMode = uvm_reg_field::type_id::create("TxFuncMode",,get_full_name());
      this.TxFuncMode.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_TxFuncMode)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_TxFuncMode


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_HMReserved0 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_HMReserved0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMReserved0 = uvm_reg_field::type_id::create("HMReserved0",,get_full_name());
      this.HMReserved0.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_HMReserved0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_HMReserved0


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_HMReservedP1_p0 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_HMReservedP1_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMReservedP1_p0 = uvm_reg_field::type_id::create("HMReservedP1_p0",,get_full_name());
      this.HMReservedP1_p0.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_HMReservedP1_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_HMReservedP1_p0


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZCalCompVref extends uvm_reg;
	rand uvm_reg_field ZCalCompVrefDAC;
	rand uvm_reg_field ReservedZCalCompVrefDAC;
	rand uvm_reg_field ZCalDACRangeSel;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalCompVrefDAC: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   ReservedZCalCompVrefDAC: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ZCalDACRangeSel: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_ZCalCompVref");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalCompVrefDAC = uvm_reg_field::type_id::create("ZCalCompVrefDAC",,get_full_name());
      this.ZCalCompVrefDAC.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 0);
      this.ReservedZCalCompVrefDAC = uvm_reg_field::type_id::create("ReservedZCalCompVrefDAC",,get_full_name());
      this.ReservedZCalCompVrefDAC.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ZCalDACRangeSel = uvm_reg_field::type_id::create("ZCalDACRangeSel",,get_full_name());
      this.ZCalDACRangeSel.configure(this, 1, 8, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZCalCompVref)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZCalCompVref


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_TxPowerDownZCAL extends uvm_reg;
	rand uvm_reg_field TxPowerDownZCAL;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxPowerDownZCAL: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_TxPowerDownZCAL");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxPowerDownZCAL = uvm_reg_field::type_id::create("TxPowerDownZCAL",,get_full_name());
      this.TxPowerDownZCAL.configure(this, 2, 0, "RW", 0, 2'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_TxPowerDownZCAL)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_TxPowerDownZCAL


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZCalCompCtrl_p0 extends uvm_reg;
	rand uvm_reg_field ZCalCompGainCurrAdj;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalCompGainCurrAdj: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_ZCalCompCtrl_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalCompGainCurrAdj = uvm_reg_field::type_id::create("ZCalCompGainCurrAdj",,get_full_name());
      this.ZCalCompGainCurrAdj.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZCalCompCtrl_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZCalCompCtrl_p0


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZCalSlewRateCtrl_p0 extends uvm_reg;
	rand uvm_reg_field ZCalTxSlewPU;
	rand uvm_reg_field ZCalTxSlewPD;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalTxSlewPU: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   ZCalTxSlewPD: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_ZCalSlewRateCtrl_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalTxSlewPU = uvm_reg_field::type_id::create("ZCalTxSlewPU",,get_full_name());
      this.ZCalTxSlewPU.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.ZCalTxSlewPD = uvm_reg_field::type_id::create("ZCalTxSlewPD",,get_full_name());
      this.ZCalTxSlewPD.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZCalSlewRateCtrl_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZCalSlewRateCtrl_p0


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_AnalogOutCtrlATO extends uvm_reg;
	rand uvm_reg_field AnalogOutCtrl;
	rand uvm_reg_field AnalogOutEn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AnalogOutCtrl: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	   AnalogOutEn: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_AnalogOutCtrlATO");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AnalogOutCtrl = uvm_reg_field::type_id::create("AnalogOutCtrl",,get_full_name());
      this.AnalogOutCtrl.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
      this.AnalogOutEn = uvm_reg_field::type_id::create("AnalogOutEn",,get_full_name());
      this.AnalogOutEn.configure(this, 1, 8, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_AnalogOutCtrlATO)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_AnalogOutCtrlATO


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ReservedATO extends uvm_reg;
	rand uvm_reg_field ReservedATO;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ReservedATO: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_ReservedATO");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ReservedATO = uvm_reg_field::type_id::create("ReservedATO",,get_full_name());
      this.ReservedATO.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ReservedATO)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ReservedATO


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_TxSeg120_p0 extends uvm_reg;
	rand uvm_reg_field TxSeg120PU0;
	rand uvm_reg_field TxSeg120PD0;
	rand uvm_reg_field TxSeg120PU1;
	rand uvm_reg_field TxSeg120PD1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxSeg120PU0: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   TxSeg120PD0: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   TxSeg120PU1: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   TxSeg120PD1: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_TxSeg120_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxSeg120PU0 = uvm_reg_field::type_id::create("TxSeg120PU0",,get_full_name());
      this.TxSeg120PU0.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.TxSeg120PD0 = uvm_reg_field::type_id::create("TxSeg120PD0",,get_full_name());
      this.TxSeg120PD0.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.TxSeg120PU1 = uvm_reg_field::type_id::create("TxSeg120PU1",,get_full_name());
      this.TxSeg120PU1.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.TxSeg120PD1 = uvm_reg_field::type_id::create("TxSeg120PD1",,get_full_name());
      this.TxSeg120PD1.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_TxSeg120_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_TxSeg120_p0


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxVrefDac_p0 extends uvm_reg;
	rand uvm_reg_field RxVrefDac_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxVrefDac_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_RxVrefDac_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxVrefDac_p0 = uvm_reg_field::type_id::create("RxVrefDac_p0",,get_full_name());
      this.RxVrefDac_p0.configure(this, 9, 0, "RW", 0, 9'hff, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxVrefDac_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxVrefDac_p0


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxDFEBiasSel extends uvm_reg;
	rand uvm_reg_field RxDFEBiasSel;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFEBiasSel: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_RxDFEBiasSel");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFEBiasSel = uvm_reg_field::type_id::create("RxDFEBiasSel",,get_full_name());
      this.RxDFEBiasSel.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxDFEBiasSel)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxDFEBiasSel


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxOffsetSelEven extends uvm_reg;
	rand uvm_reg_field RxOffsetSelEven;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxOffsetSelEven: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_RxOffsetSelEven");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxOffsetSelEven = uvm_reg_field::type_id::create("RxOffsetSelEven",,get_full_name());
      this.RxOffsetSelEven.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxOffsetSelEven)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxOffsetSelEven


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxOffsetSelOdd extends uvm_reg;
	rand uvm_reg_field RxOffsetSelOdd;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxOffsetSelOdd: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_RxOffsetSelOdd");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxOffsetSelOdd = uvm_reg_field::type_id::create("RxOffsetSelOdd",,get_full_name());
      this.RxOffsetSelOdd.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxOffsetSelOdd)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxOffsetSelOdd


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxDFETap1Sel extends uvm_reg;
	rand uvm_reg_field RxDFETap1Sel;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap1Sel: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_RxDFETap1Sel");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap1Sel = uvm_reg_field::type_id::create("RxDFETap1Sel",,get_full_name());
      this.RxDFETap1Sel.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxDFETap1Sel)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxDFETap1Sel


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxDFETap2Sel extends uvm_reg;
	rand uvm_reg_field RxDFETap2Sel;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap2Sel: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_RxDFETap2Sel");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap2Sel = uvm_reg_field::type_id::create("RxDFETap2Sel",,get_full_name());
      this.RxDFETap2Sel.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxDFETap2Sel)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxDFETap2Sel


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxAttenCtrl extends uvm_reg;
	rand uvm_reg_field RxAttenCtrl;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxAttenCtrl: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_RxAttenCtrl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxAttenCtrl = uvm_reg_field::type_id::create("RxAttenCtrl",,get_full_name());
      this.RxAttenCtrl.configure(this, 4, 0, "RW", 0, 4'h7, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxAttenCtrl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxAttenCtrl


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxCtleCtrl extends uvm_reg;
	rand uvm_reg_field RxCtleCtrl;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxCtleCtrl: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_RxCtleCtrl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxCtleCtrl = uvm_reg_field::type_id::create("RxCtleCtrl",,get_full_name());
      this.RxCtleCtrl.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxCtleCtrl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxCtleCtrl


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZCalAttDisable extends uvm_reg;
	rand uvm_reg_field ZCalAttDisable;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalAttDisable: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_ZCalAttDisable");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalAttDisable = uvm_reg_field::type_id::create("ZCalAttDisable",,get_full_name());
      this.ZCalAttDisable.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZCalAttDisable)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZCalAttDisable


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_OdtSeg120_p0 extends uvm_reg;
	rand uvm_reg_field OdtSeg120PU0;
	rand uvm_reg_field OdtSeg120PD0;
	rand uvm_reg_field OdtSeg120PU1;
	rand uvm_reg_field OdtSeg120PD1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   OdtSeg120PU0: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   OdtSeg120PD0: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   OdtSeg120PU1: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   OdtSeg120PD1: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_OdtSeg120_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.OdtSeg120PU0 = uvm_reg_field::type_id::create("OdtSeg120PU0",,get_full_name());
      this.OdtSeg120PU0.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.OdtSeg120PD0 = uvm_reg_field::type_id::create("OdtSeg120PD0",,get_full_name());
      this.OdtSeg120PD0.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.OdtSeg120PU1 = uvm_reg_field::type_id::create("OdtSeg120PU1",,get_full_name());
      this.OdtSeg120PU1.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.OdtSeg120PD1 = uvm_reg_field::type_id::create("OdtSeg120PD1",,get_full_name());
      this.OdtSeg120PD1.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_OdtSeg120_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_OdtSeg120_p0


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ReservedZCAL extends uvm_reg;
	rand uvm_reg_field ReservedZCAL;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ReservedZCAL: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_ReservedZCAL");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ReservedZCAL = uvm_reg_field::type_id::create("ReservedZCAL",,get_full_name());
      this.ReservedZCAL.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ReservedZCAL)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ReservedZCAL


class ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ReservedPZCAL_p0 extends uvm_reg;
	rand uvm_reg_field ReservedPZCAL_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ReservedPZCAL_p0: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0_ReservedPZCAL_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ReservedPZCAL_p0 = uvm_reg_field::type_id::create("ReservedPZCAL_p0",,get_full_name());
      this.ReservedPZCAL_p0.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ReservedPZCAL_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ReservedPZCAL_p0


class ral_block_DWC_DDRPHYA_HMZCAL0_p0 extends uvm_reg_block;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZcalPowerCtl ZcalPowerCtl;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxCurrAdj RxCurrAdj;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxDfeModeCfg_p0 RxDfeModeCfg_p0;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxModeCtl RxModeCtl;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxMiscCtl RxMiscCtl;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_MtestMuxSel MtestMuxSel;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_HMZCALParityInvert HMZCALParityInvert;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ScratchPadHMZCAL ScratchPadHMZCAL;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_HardMacroModeSel HardMacroModeSel;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_TxFuncMode TxFuncMode;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_HMReserved0 HMReserved0;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_HMReservedP1_p0 HMReservedP1_p0;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZCalCompVref ZCalCompVref;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_TxPowerDownZCAL TxPowerDownZCAL;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZCalCompCtrl_p0 ZCalCompCtrl_p0;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZCalSlewRateCtrl_p0 ZCalSlewRateCtrl_p0;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_AnalogOutCtrlATO AnalogOutCtrlATO;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ReservedATO ReservedATO;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_TxSeg120_p0 TxSeg120_p0;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxVrefDac_p0 RxVrefDac_p0;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxDFEBiasSel RxDFEBiasSel;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxOffsetSelEven RxOffsetSelEven;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxOffsetSelOdd RxOffsetSelOdd;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxDFETap1Sel RxDFETap1Sel;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxDFETap2Sel RxDFETap2Sel;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxAttenCtrl RxAttenCtrl;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxCtleCtrl RxCtleCtrl;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZCalAttDisable ZCalAttDisable;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_OdtSeg120_p0 OdtSeg120_p0;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ReservedZCAL ReservedZCAL;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ReservedPZCAL_p0 ReservedPZCAL_p0;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field ZcalPowerCtl_RxPowerDown;
	rand uvm_reg_field RxPowerDown;
	rand uvm_reg_field ZcalPowerCtl_RxStandby;
	rand uvm_reg_field RxStandby;
	rand uvm_reg_field RxCurrAdj_RxCurrAdj;
	rand uvm_reg_field RxDfeModeCfg_p0_RxDfeCtrl;
	rand uvm_reg_field RxDfeCtrl;
	rand uvm_reg_field RxModeCtl_RxModeCtl;
	rand uvm_reg_field RxMiscCtl_RxOffsetEn;
	rand uvm_reg_field RxOffsetEn;
	rand uvm_reg_field RxMiscCtl_RxGainCtrl;
	rand uvm_reg_field RxGainCtrl;
	rand uvm_reg_field MtestMuxSel_MtestMuxSel;
	rand uvm_reg_field HMZCALParityInvert_HMZCALParityInvert;
	rand uvm_reg_field ScratchPadHMZCAL_ScratchPadHMZCAL;
	rand uvm_reg_field HardMacroModeSel_HardMacroModeSel;
	rand uvm_reg_field TxFuncMode_TxFuncMode;
	rand uvm_reg_field HMReserved0_HMReserved0;
	rand uvm_reg_field HMReservedP1_p0_HMReservedP1_p0;
	rand uvm_reg_field ZCalCompVref_ZCalCompVrefDAC;
	rand uvm_reg_field ZCalCompVrefDAC;
	rand uvm_reg_field ZCalCompVref_ReservedZCalCompVrefDAC;
	rand uvm_reg_field ReservedZCalCompVrefDAC;
	rand uvm_reg_field ZCalCompVref_ZCalDACRangeSel;
	rand uvm_reg_field ZCalDACRangeSel;
	rand uvm_reg_field TxPowerDownZCAL_TxPowerDownZCAL;
	rand uvm_reg_field ZCalCompCtrl_p0_ZCalCompGainCurrAdj;
	rand uvm_reg_field ZCalCompGainCurrAdj;
	rand uvm_reg_field ZCalSlewRateCtrl_p0_ZCalTxSlewPU;
	rand uvm_reg_field ZCalTxSlewPU;
	rand uvm_reg_field ZCalSlewRateCtrl_p0_ZCalTxSlewPD;
	rand uvm_reg_field ZCalTxSlewPD;
	rand uvm_reg_field AnalogOutCtrlATO_AnalogOutCtrl;
	rand uvm_reg_field AnalogOutCtrl;
	rand uvm_reg_field AnalogOutCtrlATO_AnalogOutEn;
	rand uvm_reg_field AnalogOutEn;
	rand uvm_reg_field ReservedATO_ReservedATO;
	rand uvm_reg_field TxSeg120_p0_TxSeg120PU0;
	rand uvm_reg_field TxSeg120PU0;
	rand uvm_reg_field TxSeg120_p0_TxSeg120PD0;
	rand uvm_reg_field TxSeg120PD0;
	rand uvm_reg_field TxSeg120_p0_TxSeg120PU1;
	rand uvm_reg_field TxSeg120PU1;
	rand uvm_reg_field TxSeg120_p0_TxSeg120PD1;
	rand uvm_reg_field TxSeg120PD1;
	rand uvm_reg_field RxVrefDac_p0_RxVrefDac_p0;
	rand uvm_reg_field RxDFEBiasSel_RxDFEBiasSel;
	rand uvm_reg_field RxOffsetSelEven_RxOffsetSelEven;
	rand uvm_reg_field RxOffsetSelOdd_RxOffsetSelOdd;
	rand uvm_reg_field RxDFETap1Sel_RxDFETap1Sel;
	rand uvm_reg_field RxDFETap2Sel_RxDFETap2Sel;
	rand uvm_reg_field RxAttenCtrl_RxAttenCtrl;
	rand uvm_reg_field RxCtleCtrl_RxCtleCtrl;
	rand uvm_reg_field ZCalAttDisable_ZCalAttDisable;
	rand uvm_reg_field OdtSeg120_p0_OdtSeg120PU0;
	rand uvm_reg_field OdtSeg120PU0;
	rand uvm_reg_field OdtSeg120_p0_OdtSeg120PD0;
	rand uvm_reg_field OdtSeg120PD0;
	rand uvm_reg_field OdtSeg120_p0_OdtSeg120PU1;
	rand uvm_reg_field OdtSeg120PU1;
	rand uvm_reg_field OdtSeg120_p0_OdtSeg120PD1;
	rand uvm_reg_field OdtSeg120PD1;
	rand uvm_reg_field ReservedZCAL_ReservedZCAL;
	rand uvm_reg_field ReservedPZCAL_p0_ReservedPZCAL_p0;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	ZcalPowerCtl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2 };
		option.weight = 1;
	}

	RxCurrAdj : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4 };
		option.weight = 1;
	}

	RxDfeModeCfg_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h9 };
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

	MtestMuxSel : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1A };
		option.weight = 1;
	}

	HMZCALParityInvert : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4D };
		option.weight = 1;
	}

	ScratchPadHMZCAL : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h7D };
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

	ZCalCompVref : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h302 };
		option.weight = 1;
	}

	TxPowerDownZCAL : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h308 };
		option.weight = 1;
	}

	ZCalCompCtrl_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h30B };
		option.weight = 1;
	}

	ZCalSlewRateCtrl_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h30C };
		option.weight = 1;
	}

	AnalogOutCtrlATO : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h312 };
		option.weight = 1;
	}

	ReservedATO : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3AB };
		option.weight = 1;
	}

	TxSeg120_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3E0 };
		option.weight = 1;
	}

	RxVrefDac_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3E1 };
		option.weight = 1;
	}

	RxDFEBiasSel : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3E2 };
		option.weight = 1;
	}

	RxOffsetSelEven : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3E3 };
		option.weight = 1;
	}

	RxOffsetSelOdd : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3E4 };
		option.weight = 1;
	}

	RxDFETap1Sel : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3E7 };
		option.weight = 1;
	}

	RxDFETap2Sel : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3E9 };
		option.weight = 1;
	}

	RxAttenCtrl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3EC };
		option.weight = 1;
	}

	RxCtleCtrl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3ED };
		option.weight = 1;
	}

	ZCalAttDisable : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3FD };
		option.weight = 1;
	}

	OdtSeg120_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3FF };
		option.weight = 1;
	}

	ReservedZCAL : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h500 };
		option.weight = 1;
	}

	ReservedPZCAL_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h501 };
		option.weight = 1;
	}
endgroup
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p0");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.ZcalPowerCtl = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZcalPowerCtl::type_id::create("ZcalPowerCtl",,get_full_name());
      if(this.ZcalPowerCtl.has_coverage(UVM_CVR_ALL))
      	this.ZcalPowerCtl.cg_bits.option.name = {get_name(), ".", "ZcalPowerCtl_bits"};
      this.ZcalPowerCtl.configure(this, null, "");
      this.ZcalPowerCtl.build();
      this.default_map.add_reg(this.ZcalPowerCtl, `UVM_REG_ADDR_WIDTH'h2, "RW", 0);
		this.ZcalPowerCtl_RxPowerDown = this.ZcalPowerCtl.RxPowerDown;
		this.RxPowerDown = this.ZcalPowerCtl.RxPowerDown;
		this.ZcalPowerCtl_RxStandby = this.ZcalPowerCtl.RxStandby;
		this.RxStandby = this.ZcalPowerCtl.RxStandby;
      this.RxCurrAdj = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxCurrAdj::type_id::create("RxCurrAdj",,get_full_name());
      if(this.RxCurrAdj.has_coverage(UVM_CVR_ALL))
      	this.RxCurrAdj.cg_bits.option.name = {get_name(), ".", "RxCurrAdj_bits"};
      this.RxCurrAdj.configure(this, null, "");
      this.RxCurrAdj.build();
      this.default_map.add_reg(this.RxCurrAdj, `UVM_REG_ADDR_WIDTH'h4, "RW", 0);
		this.RxCurrAdj_RxCurrAdj = this.RxCurrAdj.RxCurrAdj;
      this.RxDfeModeCfg_p0 = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxDfeModeCfg_p0::type_id::create("RxDfeModeCfg_p0",,get_full_name());
      if(this.RxDfeModeCfg_p0.has_coverage(UVM_CVR_ALL))
      	this.RxDfeModeCfg_p0.cg_bits.option.name = {get_name(), ".", "RxDfeModeCfg_p0_bits"};
      this.RxDfeModeCfg_p0.configure(this, null, "");
      this.RxDfeModeCfg_p0.build();
      this.default_map.add_reg(this.RxDfeModeCfg_p0, `UVM_REG_ADDR_WIDTH'h9, "RW", 0);
		this.RxDfeModeCfg_p0_RxDfeCtrl = this.RxDfeModeCfg_p0.RxDfeCtrl;
		this.RxDfeCtrl = this.RxDfeModeCfg_p0.RxDfeCtrl;
      this.RxModeCtl = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxModeCtl::type_id::create("RxModeCtl",,get_full_name());
      if(this.RxModeCtl.has_coverage(UVM_CVR_ALL))
      	this.RxModeCtl.cg_bits.option.name = {get_name(), ".", "RxModeCtl_bits"};
      this.RxModeCtl.configure(this, null, "");
      this.RxModeCtl.build();
      this.default_map.add_reg(this.RxModeCtl, `UVM_REG_ADDR_WIDTH'hC, "RW", 0);
		this.RxModeCtl_RxModeCtl = this.RxModeCtl.RxModeCtl;
      this.RxMiscCtl = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxMiscCtl::type_id::create("RxMiscCtl",,get_full_name());
      if(this.RxMiscCtl.has_coverage(UVM_CVR_ALL))
      	this.RxMiscCtl.cg_bits.option.name = {get_name(), ".", "RxMiscCtl_bits"};
      this.RxMiscCtl.configure(this, null, "");
      this.RxMiscCtl.build();
      this.default_map.add_reg(this.RxMiscCtl, `UVM_REG_ADDR_WIDTH'hD, "RW", 0);
		this.RxMiscCtl_RxOffsetEn = this.RxMiscCtl.RxOffsetEn;
		this.RxOffsetEn = this.RxMiscCtl.RxOffsetEn;
		this.RxMiscCtl_RxGainCtrl = this.RxMiscCtl.RxGainCtrl;
		this.RxGainCtrl = this.RxMiscCtl.RxGainCtrl;
      this.MtestMuxSel = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_MtestMuxSel::type_id::create("MtestMuxSel",,get_full_name());
      if(this.MtestMuxSel.has_coverage(UVM_CVR_ALL))
      	this.MtestMuxSel.cg_bits.option.name = {get_name(), ".", "MtestMuxSel_bits"};
      this.MtestMuxSel.configure(this, null, "");
      this.MtestMuxSel.build();
      this.default_map.add_reg(this.MtestMuxSel, `UVM_REG_ADDR_WIDTH'h1A, "RW", 0);
		this.MtestMuxSel_MtestMuxSel = this.MtestMuxSel.MtestMuxSel;
      this.HMZCALParityInvert = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_HMZCALParityInvert::type_id::create("HMZCALParityInvert",,get_full_name());
      if(this.HMZCALParityInvert.has_coverage(UVM_CVR_ALL))
      	this.HMZCALParityInvert.cg_bits.option.name = {get_name(), ".", "HMZCALParityInvert_bits"};
      this.HMZCALParityInvert.configure(this, null, "");
      this.HMZCALParityInvert.build();
      this.default_map.add_reg(this.HMZCALParityInvert, `UVM_REG_ADDR_WIDTH'h4D, "RW", 0);
		this.HMZCALParityInvert_HMZCALParityInvert = this.HMZCALParityInvert.HMZCALParityInvert;
      this.ScratchPadHMZCAL = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ScratchPadHMZCAL::type_id::create("ScratchPadHMZCAL",,get_full_name());
      if(this.ScratchPadHMZCAL.has_coverage(UVM_CVR_ALL))
      	this.ScratchPadHMZCAL.cg_bits.option.name = {get_name(), ".", "ScratchPadHMZCAL_bits"};
      this.ScratchPadHMZCAL.configure(this, null, "");
      this.ScratchPadHMZCAL.build();
      this.default_map.add_reg(this.ScratchPadHMZCAL, `UVM_REG_ADDR_WIDTH'h7D, "RW", 0);
		this.ScratchPadHMZCAL_ScratchPadHMZCAL = this.ScratchPadHMZCAL.ScratchPadHMZCAL;
      this.HardMacroModeSel = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_HardMacroModeSel::type_id::create("HardMacroModeSel",,get_full_name());
      if(this.HardMacroModeSel.has_coverage(UVM_CVR_ALL))
      	this.HardMacroModeSel.cg_bits.option.name = {get_name(), ".", "HardMacroModeSel_bits"};
      this.HardMacroModeSel.configure(this, null, "");
      this.HardMacroModeSel.build();
      this.default_map.add_reg(this.HardMacroModeSel, `UVM_REG_ADDR_WIDTH'hF6, "RW", 0);
		this.HardMacroModeSel_HardMacroModeSel = this.HardMacroModeSel.HardMacroModeSel;
      this.TxFuncMode = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_TxFuncMode::type_id::create("TxFuncMode",,get_full_name());
      if(this.TxFuncMode.has_coverage(UVM_CVR_ALL))
      	this.TxFuncMode.cg_bits.option.name = {get_name(), ".", "TxFuncMode_bits"};
      this.TxFuncMode.configure(this, null, "");
      this.TxFuncMode.build();
      this.default_map.add_reg(this.TxFuncMode, `UVM_REG_ADDR_WIDTH'hF8, "RW", 0);
		this.TxFuncMode_TxFuncMode = this.TxFuncMode.TxFuncMode;
      this.HMReserved0 = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_HMReserved0::type_id::create("HMReserved0",,get_full_name());
      if(this.HMReserved0.has_coverage(UVM_CVR_ALL))
      	this.HMReserved0.cg_bits.option.name = {get_name(), ".", "HMReserved0_bits"};
      this.HMReserved0.configure(this, null, "");
      this.HMReserved0.build();
      this.default_map.add_reg(this.HMReserved0, `UVM_REG_ADDR_WIDTH'hFE, "RW", 0);
		this.HMReserved0_HMReserved0 = this.HMReserved0.HMReserved0;
      this.HMReservedP1_p0 = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_HMReservedP1_p0::type_id::create("HMReservedP1_p0",,get_full_name());
      if(this.HMReservedP1_p0.has_coverage(UVM_CVR_ALL))
      	this.HMReservedP1_p0.cg_bits.option.name = {get_name(), ".", "HMReservedP1_p0_bits"};
      this.HMReservedP1_p0.configure(this, null, "");
      this.HMReservedP1_p0.build();
      this.default_map.add_reg(this.HMReservedP1_p0, `UVM_REG_ADDR_WIDTH'hFF, "RW", 0);
		this.HMReservedP1_p0_HMReservedP1_p0 = this.HMReservedP1_p0.HMReservedP1_p0;
      this.ZCalCompVref = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZCalCompVref::type_id::create("ZCalCompVref",,get_full_name());
      if(this.ZCalCompVref.has_coverage(UVM_CVR_ALL))
      	this.ZCalCompVref.cg_bits.option.name = {get_name(), ".", "ZCalCompVref_bits"};
      this.ZCalCompVref.configure(this, null, "");
      this.ZCalCompVref.build();
      this.default_map.add_reg(this.ZCalCompVref, `UVM_REG_ADDR_WIDTH'h302, "RW", 0);
		this.ZCalCompVref_ZCalCompVrefDAC = this.ZCalCompVref.ZCalCompVrefDAC;
		this.ZCalCompVrefDAC = this.ZCalCompVref.ZCalCompVrefDAC;
		this.ZCalCompVref_ReservedZCalCompVrefDAC = this.ZCalCompVref.ReservedZCalCompVrefDAC;
		this.ReservedZCalCompVrefDAC = this.ZCalCompVref.ReservedZCalCompVrefDAC;
		this.ZCalCompVref_ZCalDACRangeSel = this.ZCalCompVref.ZCalDACRangeSel;
		this.ZCalDACRangeSel = this.ZCalCompVref.ZCalDACRangeSel;
      this.TxPowerDownZCAL = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_TxPowerDownZCAL::type_id::create("TxPowerDownZCAL",,get_full_name());
      if(this.TxPowerDownZCAL.has_coverage(UVM_CVR_ALL))
      	this.TxPowerDownZCAL.cg_bits.option.name = {get_name(), ".", "TxPowerDownZCAL_bits"};
      this.TxPowerDownZCAL.configure(this, null, "");
      this.TxPowerDownZCAL.build();
      this.default_map.add_reg(this.TxPowerDownZCAL, `UVM_REG_ADDR_WIDTH'h308, "RW", 0);
		this.TxPowerDownZCAL_TxPowerDownZCAL = this.TxPowerDownZCAL.TxPowerDownZCAL;
      this.ZCalCompCtrl_p0 = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZCalCompCtrl_p0::type_id::create("ZCalCompCtrl_p0",,get_full_name());
      if(this.ZCalCompCtrl_p0.has_coverage(UVM_CVR_ALL))
      	this.ZCalCompCtrl_p0.cg_bits.option.name = {get_name(), ".", "ZCalCompCtrl_p0_bits"};
      this.ZCalCompCtrl_p0.configure(this, null, "");
      this.ZCalCompCtrl_p0.build();
      this.default_map.add_reg(this.ZCalCompCtrl_p0, `UVM_REG_ADDR_WIDTH'h30B, "RW", 0);
		this.ZCalCompCtrl_p0_ZCalCompGainCurrAdj = this.ZCalCompCtrl_p0.ZCalCompGainCurrAdj;
		this.ZCalCompGainCurrAdj = this.ZCalCompCtrl_p0.ZCalCompGainCurrAdj;
      this.ZCalSlewRateCtrl_p0 = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZCalSlewRateCtrl_p0::type_id::create("ZCalSlewRateCtrl_p0",,get_full_name());
      if(this.ZCalSlewRateCtrl_p0.has_coverage(UVM_CVR_ALL))
      	this.ZCalSlewRateCtrl_p0.cg_bits.option.name = {get_name(), ".", "ZCalSlewRateCtrl_p0_bits"};
      this.ZCalSlewRateCtrl_p0.configure(this, null, "");
      this.ZCalSlewRateCtrl_p0.build();
      this.default_map.add_reg(this.ZCalSlewRateCtrl_p0, `UVM_REG_ADDR_WIDTH'h30C, "RW", 0);
		this.ZCalSlewRateCtrl_p0_ZCalTxSlewPU = this.ZCalSlewRateCtrl_p0.ZCalTxSlewPU;
		this.ZCalTxSlewPU = this.ZCalSlewRateCtrl_p0.ZCalTxSlewPU;
		this.ZCalSlewRateCtrl_p0_ZCalTxSlewPD = this.ZCalSlewRateCtrl_p0.ZCalTxSlewPD;
		this.ZCalTxSlewPD = this.ZCalSlewRateCtrl_p0.ZCalTxSlewPD;
      this.AnalogOutCtrlATO = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_AnalogOutCtrlATO::type_id::create("AnalogOutCtrlATO",,get_full_name());
      if(this.AnalogOutCtrlATO.has_coverage(UVM_CVR_ALL))
      	this.AnalogOutCtrlATO.cg_bits.option.name = {get_name(), ".", "AnalogOutCtrlATO_bits"};
      this.AnalogOutCtrlATO.configure(this, null, "");
      this.AnalogOutCtrlATO.build();
      this.default_map.add_reg(this.AnalogOutCtrlATO, `UVM_REG_ADDR_WIDTH'h312, "RW", 0);
		this.AnalogOutCtrlATO_AnalogOutCtrl = this.AnalogOutCtrlATO.AnalogOutCtrl;
		this.AnalogOutCtrl = this.AnalogOutCtrlATO.AnalogOutCtrl;
		this.AnalogOutCtrlATO_AnalogOutEn = this.AnalogOutCtrlATO.AnalogOutEn;
		this.AnalogOutEn = this.AnalogOutCtrlATO.AnalogOutEn;
      this.ReservedATO = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ReservedATO::type_id::create("ReservedATO",,get_full_name());
      if(this.ReservedATO.has_coverage(UVM_CVR_ALL))
      	this.ReservedATO.cg_bits.option.name = {get_name(), ".", "ReservedATO_bits"};
      this.ReservedATO.configure(this, null, "");
      this.ReservedATO.build();
      this.default_map.add_reg(this.ReservedATO, `UVM_REG_ADDR_WIDTH'h3AB, "RW", 0);
		this.ReservedATO_ReservedATO = this.ReservedATO.ReservedATO;
      this.TxSeg120_p0 = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_TxSeg120_p0::type_id::create("TxSeg120_p0",,get_full_name());
      if(this.TxSeg120_p0.has_coverage(UVM_CVR_ALL))
      	this.TxSeg120_p0.cg_bits.option.name = {get_name(), ".", "TxSeg120_p0_bits"};
      this.TxSeg120_p0.configure(this, null, "");
      this.TxSeg120_p0.build();
      this.default_map.add_reg(this.TxSeg120_p0, `UVM_REG_ADDR_WIDTH'h3E0, "RW", 0);
		this.TxSeg120_p0_TxSeg120PU0 = this.TxSeg120_p0.TxSeg120PU0;
		this.TxSeg120PU0 = this.TxSeg120_p0.TxSeg120PU0;
		this.TxSeg120_p0_TxSeg120PD0 = this.TxSeg120_p0.TxSeg120PD0;
		this.TxSeg120PD0 = this.TxSeg120_p0.TxSeg120PD0;
		this.TxSeg120_p0_TxSeg120PU1 = this.TxSeg120_p0.TxSeg120PU1;
		this.TxSeg120PU1 = this.TxSeg120_p0.TxSeg120PU1;
		this.TxSeg120_p0_TxSeg120PD1 = this.TxSeg120_p0.TxSeg120PD1;
		this.TxSeg120PD1 = this.TxSeg120_p0.TxSeg120PD1;
      this.RxVrefDac_p0 = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxVrefDac_p0::type_id::create("RxVrefDac_p0",,get_full_name());
      if(this.RxVrefDac_p0.has_coverage(UVM_CVR_ALL))
      	this.RxVrefDac_p0.cg_bits.option.name = {get_name(), ".", "RxVrefDac_p0_bits"};
      this.RxVrefDac_p0.configure(this, null, "");
      this.RxVrefDac_p0.build();
      this.default_map.add_reg(this.RxVrefDac_p0, `UVM_REG_ADDR_WIDTH'h3E1, "RW", 0);
		this.RxVrefDac_p0_RxVrefDac_p0 = this.RxVrefDac_p0.RxVrefDac_p0;
      this.RxDFEBiasSel = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxDFEBiasSel::type_id::create("RxDFEBiasSel",,get_full_name());
      if(this.RxDFEBiasSel.has_coverage(UVM_CVR_ALL))
      	this.RxDFEBiasSel.cg_bits.option.name = {get_name(), ".", "RxDFEBiasSel_bits"};
      this.RxDFEBiasSel.configure(this, null, "");
      this.RxDFEBiasSel.build();
      this.default_map.add_reg(this.RxDFEBiasSel, `UVM_REG_ADDR_WIDTH'h3E2, "RW", 0);
		this.RxDFEBiasSel_RxDFEBiasSel = this.RxDFEBiasSel.RxDFEBiasSel;
      this.RxOffsetSelEven = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxOffsetSelEven::type_id::create("RxOffsetSelEven",,get_full_name());
      if(this.RxOffsetSelEven.has_coverage(UVM_CVR_ALL))
      	this.RxOffsetSelEven.cg_bits.option.name = {get_name(), ".", "RxOffsetSelEven_bits"};
      this.RxOffsetSelEven.configure(this, null, "");
      this.RxOffsetSelEven.build();
      this.default_map.add_reg(this.RxOffsetSelEven, `UVM_REG_ADDR_WIDTH'h3E3, "RW", 0);
		this.RxOffsetSelEven_RxOffsetSelEven = this.RxOffsetSelEven.RxOffsetSelEven;
      this.RxOffsetSelOdd = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxOffsetSelOdd::type_id::create("RxOffsetSelOdd",,get_full_name());
      if(this.RxOffsetSelOdd.has_coverage(UVM_CVR_ALL))
      	this.RxOffsetSelOdd.cg_bits.option.name = {get_name(), ".", "RxOffsetSelOdd_bits"};
      this.RxOffsetSelOdd.configure(this, null, "");
      this.RxOffsetSelOdd.build();
      this.default_map.add_reg(this.RxOffsetSelOdd, `UVM_REG_ADDR_WIDTH'h3E4, "RW", 0);
		this.RxOffsetSelOdd_RxOffsetSelOdd = this.RxOffsetSelOdd.RxOffsetSelOdd;
      this.RxDFETap1Sel = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxDFETap1Sel::type_id::create("RxDFETap1Sel",,get_full_name());
      if(this.RxDFETap1Sel.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap1Sel.cg_bits.option.name = {get_name(), ".", "RxDFETap1Sel_bits"};
      this.RxDFETap1Sel.configure(this, null, "");
      this.RxDFETap1Sel.build();
      this.default_map.add_reg(this.RxDFETap1Sel, `UVM_REG_ADDR_WIDTH'h3E7, "RW", 0);
		this.RxDFETap1Sel_RxDFETap1Sel = this.RxDFETap1Sel.RxDFETap1Sel;
      this.RxDFETap2Sel = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxDFETap2Sel::type_id::create("RxDFETap2Sel",,get_full_name());
      if(this.RxDFETap2Sel.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap2Sel.cg_bits.option.name = {get_name(), ".", "RxDFETap2Sel_bits"};
      this.RxDFETap2Sel.configure(this, null, "");
      this.RxDFETap2Sel.build();
      this.default_map.add_reg(this.RxDFETap2Sel, `UVM_REG_ADDR_WIDTH'h3E9, "RW", 0);
		this.RxDFETap2Sel_RxDFETap2Sel = this.RxDFETap2Sel.RxDFETap2Sel;
      this.RxAttenCtrl = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxAttenCtrl::type_id::create("RxAttenCtrl",,get_full_name());
      if(this.RxAttenCtrl.has_coverage(UVM_CVR_ALL))
      	this.RxAttenCtrl.cg_bits.option.name = {get_name(), ".", "RxAttenCtrl_bits"};
      this.RxAttenCtrl.configure(this, null, "");
      this.RxAttenCtrl.build();
      this.default_map.add_reg(this.RxAttenCtrl, `UVM_REG_ADDR_WIDTH'h3EC, "RW", 0);
		this.RxAttenCtrl_RxAttenCtrl = this.RxAttenCtrl.RxAttenCtrl;
      this.RxCtleCtrl = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_RxCtleCtrl::type_id::create("RxCtleCtrl",,get_full_name());
      if(this.RxCtleCtrl.has_coverage(UVM_CVR_ALL))
      	this.RxCtleCtrl.cg_bits.option.name = {get_name(), ".", "RxCtleCtrl_bits"};
      this.RxCtleCtrl.configure(this, null, "");
      this.RxCtleCtrl.build();
      this.default_map.add_reg(this.RxCtleCtrl, `UVM_REG_ADDR_WIDTH'h3ED, "RW", 0);
		this.RxCtleCtrl_RxCtleCtrl = this.RxCtleCtrl.RxCtleCtrl;
      this.ZCalAttDisable = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ZCalAttDisable::type_id::create("ZCalAttDisable",,get_full_name());
      if(this.ZCalAttDisable.has_coverage(UVM_CVR_ALL))
      	this.ZCalAttDisable.cg_bits.option.name = {get_name(), ".", "ZCalAttDisable_bits"};
      this.ZCalAttDisable.configure(this, null, "");
      this.ZCalAttDisable.build();
      this.default_map.add_reg(this.ZCalAttDisable, `UVM_REG_ADDR_WIDTH'h3FD, "RW", 0);
		this.ZCalAttDisable_ZCalAttDisable = this.ZCalAttDisable.ZCalAttDisable;
      this.OdtSeg120_p0 = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_OdtSeg120_p0::type_id::create("OdtSeg120_p0",,get_full_name());
      if(this.OdtSeg120_p0.has_coverage(UVM_CVR_ALL))
      	this.OdtSeg120_p0.cg_bits.option.name = {get_name(), ".", "OdtSeg120_p0_bits"};
      this.OdtSeg120_p0.configure(this, null, "");
      this.OdtSeg120_p0.build();
      this.default_map.add_reg(this.OdtSeg120_p0, `UVM_REG_ADDR_WIDTH'h3FF, "RW", 0);
		this.OdtSeg120_p0_OdtSeg120PU0 = this.OdtSeg120_p0.OdtSeg120PU0;
		this.OdtSeg120PU0 = this.OdtSeg120_p0.OdtSeg120PU0;
		this.OdtSeg120_p0_OdtSeg120PD0 = this.OdtSeg120_p0.OdtSeg120PD0;
		this.OdtSeg120PD0 = this.OdtSeg120_p0.OdtSeg120PD0;
		this.OdtSeg120_p0_OdtSeg120PU1 = this.OdtSeg120_p0.OdtSeg120PU1;
		this.OdtSeg120PU1 = this.OdtSeg120_p0.OdtSeg120PU1;
		this.OdtSeg120_p0_OdtSeg120PD1 = this.OdtSeg120_p0.OdtSeg120PD1;
		this.OdtSeg120PD1 = this.OdtSeg120_p0.OdtSeg120PD1;
      this.ReservedZCAL = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ReservedZCAL::type_id::create("ReservedZCAL",,get_full_name());
      if(this.ReservedZCAL.has_coverage(UVM_CVR_ALL))
      	this.ReservedZCAL.cg_bits.option.name = {get_name(), ".", "ReservedZCAL_bits"};
      this.ReservedZCAL.configure(this, null, "");
      this.ReservedZCAL.build();
      this.default_map.add_reg(this.ReservedZCAL, `UVM_REG_ADDR_WIDTH'h500, "RW", 0);
		this.ReservedZCAL_ReservedZCAL = this.ReservedZCAL.ReservedZCAL;
      this.ReservedPZCAL_p0 = ral_reg_DWC_DDRPHYA_HMZCAL0_p0_ReservedPZCAL_p0::type_id::create("ReservedPZCAL_p0",,get_full_name());
      if(this.ReservedPZCAL_p0.has_coverage(UVM_CVR_ALL))
      	this.ReservedPZCAL_p0.cg_bits.option.name = {get_name(), ".", "ReservedPZCAL_p0_bits"};
      this.ReservedPZCAL_p0.configure(this, null, "");
      this.ReservedPZCAL_p0.build();
      this.default_map.add_reg(this.ReservedPZCAL_p0, `UVM_REG_ADDR_WIDTH'h501, "RW", 0);
		this.ReservedPZCAL_p0_ReservedPZCAL_p0 = this.ReservedPZCAL_p0.ReservedPZCAL_p0;
   endfunction : build

	`uvm_object_utils(ral_block_DWC_DDRPHYA_HMZCAL0_p0)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_DDRPHYA_HMZCAL0_p0


endpackage
`endif
