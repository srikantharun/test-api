`ifndef RAL_DWC_DDRPHYA_HMAC1_P0_PKG
`define RAL_DWC_DDRPHYA_HMAC1_P0_PKG

package ral_DWC_DDRPHYA_HMAC1_p0_pkg;
import uvm_pkg::*;

class ral_reg_DWC_DDRPHYA_HMAC1_p0_AnibRcvPtrInitValS0 extends uvm_reg;
	rand uvm_reg_field AnibRcvPtrInitValS0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AnibRcvPtrInitValS0: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_AnibRcvPtrInitValS0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AnibRcvPtrInitValS0 = uvm_reg_field::type_id::create("AnibRcvPtrInitValS0",,get_full_name());
      this.AnibRcvPtrInitValS0.configure(this, 3, 0, "RW", 0, 3'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_AnibRcvPtrInitValS0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_AnibRcvPtrInitValS0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_AnibRcvPtrInitValS1 extends uvm_reg;
	rand uvm_reg_field AnibRcvPtrInitValS1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AnibRcvPtrInitValS1: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_AnibRcvPtrInitValS1");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AnibRcvPtrInitValS1 = uvm_reg_field::type_id::create("AnibRcvPtrInitValS1",,get_full_name());
      this.AnibRcvPtrInitValS1.configure(this, 3, 0, "RW", 0, 3'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_AnibRcvPtrInitValS1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_AnibRcvPtrInitValS1


class ral_reg_DWC_DDRPHYA_HMAC1_p0_RxPowerDownAC extends uvm_reg;
	rand uvm_reg_field RxPowerDownAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxPowerDownAC: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_RxPowerDownAC");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxPowerDownAC = uvm_reg_field::type_id::create("RxPowerDownAC",,get_full_name());
      this.RxPowerDownAC.configure(this, 2, 0, "RW", 0, 2'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_RxPowerDownAC)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_RxPowerDownAC


class ral_reg_DWC_DDRPHYA_HMAC1_p0_ACRxClkEn extends uvm_reg;
	rand uvm_reg_field ACRxClkEn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACRxClkEn: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_ACRxClkEn");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACRxClkEn = uvm_reg_field::type_id::create("ACRxClkEn",,get_full_name());
      this.ACRxClkEn.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_ACRxClkEn)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_ACRxClkEn


class ral_reg_DWC_DDRPHYA_HMAC1_p0_CKDllControl extends uvm_reg;
	rand uvm_reg_field CKDllControl;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CKDllControl: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_CKDllControl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CKDllControl = uvm_reg_field::type_id::create("CKDllControl",,get_full_name());
      this.CKDllControl.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_CKDllControl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_CKDllControl


class ral_reg_DWC_DDRPHYA_HMAC1_p0_MtestMuxSel extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_MtestMuxSel");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MtestMuxSel = uvm_reg_field::type_id::create("MtestMuxSel",,get_full_name());
      this.MtestMuxSel.configure(this, 10, 0, "RW", 0, 10'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_MtestMuxSel)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_MtestMuxSel


class ral_reg_DWC_DDRPHYA_HMAC1_p0_NeverGateACDlyCalValClk extends uvm_reg;
	rand uvm_reg_field NeverGateACDlyCalValClk;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   NeverGateACDlyCalValClk: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_NeverGateACDlyCalValClk");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.NeverGateACDlyCalValClk = uvm_reg_field::type_id::create("NeverGateACDlyCalValClk",,get_full_name());
      this.NeverGateACDlyCalValClk.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_NeverGateACDlyCalValClk)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_NeverGateACDlyCalValClk


class ral_reg_DWC_DDRPHYA_HMAC1_p0_NeverGateACDlyScaleValClk extends uvm_reg;
	rand uvm_reg_field NeverGateACDlyScaleValClk;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   NeverGateACDlyScaleValClk: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_NeverGateACDlyScaleValClk");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.NeverGateACDlyScaleValClk = uvm_reg_field::type_id::create("NeverGateACDlyScaleValClk",,get_full_name());
      this.NeverGateACDlyScaleValClk.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_NeverGateACDlyScaleValClk)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_NeverGateACDlyScaleValClk


class ral_reg_DWC_DDRPHYA_HMAC1_p0_ACReserved extends uvm_reg;
	rand uvm_reg_field ReservedACS;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ReservedACS: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_ACReserved");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ReservedACS = uvm_reg_field::type_id::create("ReservedACS",,get_full_name());
      this.ReservedACS.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_ACReserved)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_ACReserved


class ral_reg_DWC_DDRPHYA_HMAC1_p0_ACReservedP_p0 extends uvm_reg;
	rand uvm_reg_field ReservedACPS;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ReservedACPS: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_ACReservedP_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ReservedACPS = uvm_reg_field::type_id::create("ReservedACPS",,get_full_name());
      this.ReservedACPS.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_ACReservedP_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_ACReservedP_p0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_HMACParityInvert extends uvm_reg;
	rand uvm_reg_field HMACParityInvert;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HMACParityInvert: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_HMACParityInvert");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMACParityInvert = uvm_reg_field::type_id::create("HMACParityInvert",,get_full_name());
      this.HMACParityInvert.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_HMACParityInvert)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_HMACParityInvert


class ral_reg_DWC_DDRPHYA_HMAC1_p0_HMLcdlStatusSel extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_HMLcdlStatusSel");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_HMLcdlStatusSel)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_HMLcdlStatusSel


class ral_reg_DWC_DDRPHYA_HMAC1_p0_HMLcdlStatus extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_HMLcdlStatus");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_HMLcdlStatus)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_HMLcdlStatus


class ral_reg_DWC_DDRPHYA_HMAC1_p0_HMTxLcdlSeed_p0 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_HMTxLcdlSeed_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMTxLcdlSeed_p0 = uvm_reg_field::type_id::create("HMTxLcdlSeed_p0",,get_full_name());
      this.HMTxLcdlSeed_p0.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_HMTxLcdlSeed_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_HMTxLcdlSeed_p0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_HMACLcdlCalDeltaStepEn extends uvm_reg;
	rand uvm_reg_field TxLcdlCalDeltaStepEn;
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
	endgroup
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_HMACLcdlCalDeltaStepEn");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxLcdlCalDeltaStepEn = uvm_reg_field::type_id::create("TxLcdlCalDeltaStepEn",,get_full_name());
      this.TxLcdlCalDeltaStepEn.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_HMACLcdlCalDeltaStepEn)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_HMACLcdlCalDeltaStepEn


class ral_reg_DWC_DDRPHYA_HMAC1_p0_LcdlMonitorCtl_p0 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_LcdlMonitorCtl_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.StickyUnlckThrshld = uvm_reg_field::type_id::create("StickyUnlckThrshld",,get_full_name());
      this.StickyUnlckThrshld.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_LcdlMonitorCtl_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_LcdlMonitorCtl_p0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_HMACLcdlCalDeltaMM_p0 extends uvm_reg;
	rand uvm_reg_field TxLcdlCalDeltaMM;
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
	endgroup
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_HMACLcdlCalDeltaMM_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxLcdlCalDeltaMM = uvm_reg_field::type_id::create("TxLcdlCalDeltaMM",,get_full_name());
      this.TxLcdlCalDeltaMM.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_HMACLcdlCalDeltaMM_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_HMACLcdlCalDeltaMM_p0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_TxACDcaModeLn0_p0 extends uvm_reg;
	rand uvm_reg_field TxACDcaModeLn0_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxACDcaModeLn0_p0: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_TxACDcaModeLn0_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxACDcaModeLn0_p0 = uvm_reg_field::type_id::create("TxACDcaModeLn0_p0",,get_full_name());
      this.TxACDcaModeLn0_p0.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_TxACDcaModeLn0_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_TxACDcaModeLn0_p0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_TxACDcaModeLn1_p0 extends uvm_reg;
	rand uvm_reg_field TxACDcaModeLn1_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxACDcaModeLn1_p0: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_TxACDcaModeLn1_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxACDcaModeLn1_p0 = uvm_reg_field::type_id::create("TxACDcaModeLn1_p0",,get_full_name());
      this.TxACDcaModeLn1_p0.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_TxACDcaModeLn1_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_TxACDcaModeLn1_p0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_TxModeCtlAC extends uvm_reg;
	rand uvm_reg_field TxModeCtlAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxModeCtlAC: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_TxModeCtlAC");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxModeCtlAC = uvm_reg_field::type_id::create("TxModeCtlAC",,get_full_name());
      this.TxModeCtlAC.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_TxModeCtlAC)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_TxModeCtlAC


class ral_reg_DWC_DDRPHYA_HMAC1_p0_TxSlewAC_p0 extends uvm_reg;
	rand uvm_reg_field TxSlewPUAC;
	rand uvm_reg_field TxSlewPDAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxSlewPUAC: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   TxSlewPDAC: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_TxSlewAC_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxSlewPUAC = uvm_reg_field::type_id::create("TxSlewPUAC",,get_full_name());
      this.TxSlewPUAC.configure(this, 4, 0, "RW", 0, 4'h1, 1, 0, 0);
      this.TxSlewPDAC = uvm_reg_field::type_id::create("TxSlewPDAC",,get_full_name());
      this.TxSlewPDAC.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_TxSlewAC_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_TxSlewAC_p0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_TxImpedanceAC_p0 extends uvm_reg;
	rand uvm_reg_field TxStrenCodePUAC;
	rand uvm_reg_field TxStrenCodePDAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxStrenCodePUAC: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   TxStrenCodePDAC: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_TxImpedanceAC_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxStrenCodePUAC = uvm_reg_field::type_id::create("TxStrenCodePUAC",,get_full_name());
      this.TxStrenCodePUAC.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.TxStrenCodePDAC = uvm_reg_field::type_id::create("TxStrenCodePDAC",,get_full_name());
      this.TxStrenCodePDAC.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_TxImpedanceAC_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_TxImpedanceAC_p0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_TxAcDcaCtrl0 extends uvm_reg;
	rand uvm_reg_field TxACDcaCoarse0;
	rand uvm_reg_field TxACDcaFinePU0;
	rand uvm_reg_field TxACDcaFinePD0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxACDcaCoarse0: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   TxACDcaFinePU0: coverpoint {m_data[5:2], m_is_read} iff(m_be) {
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
	   TxACDcaFinePD0: coverpoint {m_data[9:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_TxAcDcaCtrl0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxACDcaCoarse0 = uvm_reg_field::type_id::create("TxACDcaCoarse0",,get_full_name());
      this.TxACDcaCoarse0.configure(this, 2, 0, "RW", 0, 2'h3, 1, 0, 0);
      this.TxACDcaFinePU0 = uvm_reg_field::type_id::create("TxACDcaFinePU0",,get_full_name());
      this.TxACDcaFinePU0.configure(this, 4, 2, "RW", 0, 4'h6, 1, 0, 0);
      this.TxACDcaFinePD0 = uvm_reg_field::type_id::create("TxACDcaFinePD0",,get_full_name());
      this.TxACDcaFinePD0.configure(this, 4, 6, "RW", 0, 4'h6, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_TxAcDcaCtrl0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_TxAcDcaCtrl0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_TxAcDcaCtrl1 extends uvm_reg;
	rand uvm_reg_field TxACDcaCoarse1;
	rand uvm_reg_field TxACDcaFinePU1;
	rand uvm_reg_field TxACDcaFinePD1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxACDcaCoarse1: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   TxACDcaFinePU1: coverpoint {m_data[5:2], m_is_read} iff(m_be) {
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
	   TxACDcaFinePD1: coverpoint {m_data[9:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_TxAcDcaCtrl1");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxACDcaCoarse1 = uvm_reg_field::type_id::create("TxACDcaCoarse1",,get_full_name());
      this.TxACDcaCoarse1.configure(this, 2, 0, "RW", 0, 2'h3, 1, 0, 0);
      this.TxACDcaFinePU1 = uvm_reg_field::type_id::create("TxACDcaFinePU1",,get_full_name());
      this.TxACDcaFinePU1.configure(this, 4, 2, "RW", 0, 4'h6, 1, 0, 0);
      this.TxACDcaFinePD1 = uvm_reg_field::type_id::create("TxACDcaFinePD1",,get_full_name());
      this.TxACDcaFinePD1.configure(this, 4, 6, "RW", 0, 4'h6, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_TxAcDcaCtrl1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_TxAcDcaCtrl1


class ral_reg_DWC_DDRPHYA_HMAC1_p0_OdtImpedanceAC_p0 extends uvm_reg;
	rand uvm_reg_field OdtStrenCodePUAC;
	rand uvm_reg_field OdtStrenCodePDAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   OdtStrenCodePUAC: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   OdtStrenCodePDAC: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_OdtImpedanceAC_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.OdtStrenCodePUAC = uvm_reg_field::type_id::create("OdtStrenCodePUAC",,get_full_name());
      this.OdtStrenCodePUAC.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.OdtStrenCodePDAC = uvm_reg_field::type_id::create("OdtStrenCodePDAC",,get_full_name());
      this.OdtStrenCodePDAC.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_OdtImpedanceAC_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_OdtImpedanceAC_p0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_ScratchPadHMAC extends uvm_reg;
	rand uvm_reg_field ScratchPadHMAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ScratchPadHMAC: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_ScratchPadHMAC");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ScratchPadHMAC = uvm_reg_field::type_id::create("ScratchPadHMAC",,get_full_name());
      this.ScratchPadHMAC.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_ScratchPadHMAC)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_ScratchPadHMAC


class ral_reg_DWC_DDRPHYA_HMAC1_p0_AcCoreLoopBackMode extends uvm_reg;
	rand uvm_reg_field AcCoreLoopBackMode;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcCoreLoopBackMode: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_AcCoreLoopBackMode");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcCoreLoopBackMode = uvm_reg_field::type_id::create("AcCoreLoopBackMode",,get_full_name());
      this.AcCoreLoopBackMode.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_AcCoreLoopBackMode)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_AcCoreLoopBackMode


class ral_reg_DWC_DDRPHYA_HMAC1_p0_RxAcAttenCtrlLn0 extends uvm_reg;
	rand uvm_reg_field RxAcAttenCtrlLn0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxAcAttenCtrlLn0: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_RxAcAttenCtrlLn0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxAcAttenCtrlLn0 = uvm_reg_field::type_id::create("RxAcAttenCtrlLn0",,get_full_name());
      this.RxAcAttenCtrlLn0.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_RxAcAttenCtrlLn0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_RxAcAttenCtrlLn0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_RxAcAttenCtrlLn1 extends uvm_reg;
	rand uvm_reg_field RxAcAttenCtrlLn1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxAcAttenCtrlLn1: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_RxAcAttenCtrlLn1");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxAcAttenCtrlLn1 = uvm_reg_field::type_id::create("RxAcAttenCtrlLn1",,get_full_name());
      this.RxAcAttenCtrlLn1.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_RxAcAttenCtrlLn1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_RxAcAttenCtrlLn1


class ral_reg_DWC_DDRPHYA_HMAC1_p0_LcdlTstPhase extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_LcdlTstPhase");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.LcdlTstPhase = uvm_reg_field::type_id::create("LcdlTstPhase",,get_full_name());
      this.LcdlTstPhase.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_LcdlTstPhase)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_LcdlTstPhase


class ral_reg_DWC_DDRPHYA_HMAC1_p0_HardMacroModeSel extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_HardMacroModeSel");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HardMacroModeSel = uvm_reg_field::type_id::create("HardMacroModeSel",,get_full_name());
      this.HardMacroModeSel.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_HardMacroModeSel)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_HardMacroModeSel


class ral_reg_DWC_DDRPHYA_HMAC1_p0_TxFuncMode extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_TxFuncMode");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxFuncMode = uvm_reg_field::type_id::create("TxFuncMode",,get_full_name());
      this.TxFuncMode.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_TxFuncMode)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_TxFuncMode


class ral_reg_DWC_DDRPHYA_HMAC1_p0_HMReserved0 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_HMReserved0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMReserved0 = uvm_reg_field::type_id::create("HMReserved0",,get_full_name());
      this.HMReserved0.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_HMReserved0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_HMReserved0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_HMReservedP1_p0 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_HMReservedP1_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMReservedP1_p0 = uvm_reg_field::type_id::create("HMReservedP1_p0",,get_full_name());
      this.HMReservedP1_p0.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_HMReservedP1_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_HMReservedP1_p0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCATxLcdlPhase_p0 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_PclkDCATxLcdlPhase_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCATxLcdlPhase_p0 = uvm_reg_field::type_id::create("PclkDCATxLcdlPhase_p0",,get_full_name());
      this.PclkDCATxLcdlPhase_p0.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCATxLcdlPhase_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCATxLcdlPhase_p0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACalSampAC0 extends uvm_reg;
	uvm_reg_field PclkDCACalSampAC0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACalSampAC0: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_PclkDCACalSampAC0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACalSampAC0 = uvm_reg_field::type_id::create("PclkDCACalSampAC0",,get_full_name());
      this.PclkDCACalSampAC0.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACalSampAC0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACalSampAC0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACalSampAC1 extends uvm_reg;
	uvm_reg_field PclkDCACalSampAC1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACalSampAC1: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_PclkDCACalSampAC1");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACalSampAC1 = uvm_reg_field::type_id::create("PclkDCACalSampAC1",,get_full_name());
      this.PclkDCACalSampAC1.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACalSampAC1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACalSampAC1


class ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAResults extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_PclkDCAResults");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAResults)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAResults


class ral_reg_DWC_DDRPHYA_HMAC1_p0_ACXPowerDownLn0 extends uvm_reg;
	rand uvm_reg_field AcTxPowerDownLn0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcTxPowerDownLn0: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_ACXPowerDownLn0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcTxPowerDownLn0 = uvm_reg_field::type_id::create("AcTxPowerDownLn0",,get_full_name());
      this.AcTxPowerDownLn0.configure(this, 2, 0, "RW", 0, 2'h2, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_ACXPowerDownLn0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_ACXPowerDownLn0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_ACXPowerDownLn1 extends uvm_reg;
	rand uvm_reg_field AcTxPowerDownLn1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcTxPowerDownLn1: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_ACXPowerDownLn1");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcTxPowerDownLn1 = uvm_reg_field::type_id::create("AcTxPowerDownLn1",,get_full_name());
      this.AcTxPowerDownLn1.configure(this, 2, 0, "RW", 0, 2'h2, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_ACXPowerDownLn1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_ACXPowerDownLn1


class ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAStaticCtrl1AC_p0 extends uvm_reg;
	rand uvm_reg_field PclkDCAInvertSampAC;
	rand uvm_reg_field PclkDCALcdlEn4pAC;
	rand uvm_reg_field PclkDCDMissionModeDelayAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCAInvertSampAC: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PclkDCALcdlEn4pAC: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PclkDCDMissionModeDelayAC: coverpoint {m_data[8:2], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_PclkDCAStaticCtrl1AC_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCAInvertSampAC = uvm_reg_field::type_id::create("PclkDCAInvertSampAC",,get_full_name());
      this.PclkDCAInvertSampAC.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.PclkDCALcdlEn4pAC = uvm_reg_field::type_id::create("PclkDCALcdlEn4pAC",,get_full_name());
      this.PclkDCALcdlEn4pAC.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.PclkDCDMissionModeDelayAC = uvm_reg_field::type_id::create("PclkDCDMissionModeDelayAC",,get_full_name());
      this.PclkDCDMissionModeDelayAC.configure(this, 7, 2, "RW", 0, 7'h4, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAStaticCtrl1AC_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAStaticCtrl1AC_p0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCASampDelayLCDLAC_p0 extends uvm_reg;
	rand uvm_reg_field PclkDCASampDelayLCDLAC_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCASampDelayLCDLAC_p0: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_PclkDCASampDelayLCDLAC_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCASampDelayLCDLAC_p0 = uvm_reg_field::type_id::create("PclkDCASampDelayLCDLAC_p0",,get_full_name());
      this.PclkDCASampDelayLCDLAC_p0.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCASampDelayLCDLAC_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCASampDelayLCDLAC_p0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAStatusSel extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_PclkDCAStatusSel");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAStatusSel)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAStatusSel


class ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAStatusInfo extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_PclkDCAStatusInfo");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCAStatusInfo = uvm_reg_field::type_id::create("PclkDCAStatusInfo",,get_full_name());
      this.PclkDCAStatusInfo.configure(this, 12, 0, "RO", 1, 12'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAStatusInfo)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAStatusInfo


class ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACoarseBoundAC extends uvm_reg;
	rand uvm_reg_field PclkDCAMaxCoarseAC;
	rand uvm_reg_field PclkDCAMinCoarseAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCAMaxCoarseAC: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	   PclkDCAMinCoarseAC: coverpoint {m_data[9:5], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_PclkDCACoarseBoundAC");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCAMaxCoarseAC = uvm_reg_field::type_id::create("PclkDCAMaxCoarseAC",,get_full_name());
      this.PclkDCAMaxCoarseAC.configure(this, 5, 0, "RW", 0, 5'h4, 1, 0, 0);
      this.PclkDCAMinCoarseAC = uvm_reg_field::type_id::create("PclkDCAMinCoarseAC",,get_full_name());
      this.PclkDCAMinCoarseAC.configure(this, 5, 5, "RW", 0, 5'h14, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACoarseBoundAC)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACoarseBoundAC


class ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAMiscCtrlAC extends uvm_reg;
	rand uvm_reg_field PclkDCADitherModeAC;
	rand uvm_reg_field PclkDCDForceCkEnAC;
	rand uvm_reg_field PclkDCAReservedAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCADitherModeAC: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PclkDCDForceCkEnAC: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PclkDCAReservedAC: coverpoint {m_data[8:2], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_PclkDCAMiscCtrlAC");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCADitherModeAC = uvm_reg_field::type_id::create("PclkDCADitherModeAC",,get_full_name());
      this.PclkDCADitherModeAC.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.PclkDCDForceCkEnAC = uvm_reg_field::type_id::create("PclkDCDForceCkEnAC",,get_full_name());
      this.PclkDCDForceCkEnAC.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.PclkDCAReservedAC = uvm_reg_field::type_id::create("PclkDCAReservedAC",,get_full_name());
      this.PclkDCAReservedAC.configure(this, 7, 2, "RW", 0, 7'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAMiscCtrlAC)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAMiscCtrlAC


class ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCDOffsetAC0_p0 extends uvm_reg;
	rand uvm_reg_field PclkDCDOffsetAC0_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCDOffsetAC0_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_PclkDCDOffsetAC0_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCDOffsetAC0_p0 = uvm_reg_field::type_id::create("PclkDCDOffsetAC0_p0",,get_full_name());
      this.PclkDCDOffsetAC0_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCDOffsetAC0_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCDOffsetAC0_p0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCDOffsetAC1_p0 extends uvm_reg;
	rand uvm_reg_field PclkDCDOffsetAC1_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCDOffsetAC1_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_PclkDCDOffsetAC1_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCDOffsetAC1_p0 = uvm_reg_field::type_id::create("PclkDCDOffsetAC1_p0",,get_full_name());
      this.PclkDCDOffsetAC1_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCDOffsetAC1_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCDOffsetAC1_p0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCALcdlCalCtrl extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_PclkDCALcdlCalCtrl");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCALcdlCalCtrl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCALcdlCalCtrl


class ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestCntRingOscSelACX extends uvm_reg;
	rand uvm_reg_field DlyTestCntRingOscSelACX;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DlyTestCntRingOscSelACX: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_DlyTestCntRingOscSelACX");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DlyTestCntRingOscSelACX = uvm_reg_field::type_id::create("DlyTestCntRingOscSelACX",,get_full_name());
      this.DlyTestCntRingOscSelACX.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestCntRingOscSelACX)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestCntRingOscSelACX


class ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestRingSelACX extends uvm_reg;
	rand uvm_reg_field DlyTestRingSelACX;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DlyTestRingSelACX: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_DlyTestRingSelACX");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DlyTestRingSelACX = uvm_reg_field::type_id::create("DlyTestRingSelACX",,get_full_name());
      this.DlyTestRingSelACX.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestRingSelACX)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestRingSelACX


class ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestCntDfiClkIVHM extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_DlyTestCntDfiClkIVHM");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DlyTestCntDfiClkIVHM = uvm_reg_field::type_id::create("DlyTestCntDfiClkIVHM",,get_full_name());
      this.DlyTestCntDfiClkIVHM.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestCntDfiClkIVHM)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestCntDfiClkIVHM


class ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestCntDfiClkHM extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_DlyTestCntDfiClkHM");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DlyTestCntDfiClkHM = uvm_reg_field::type_id::create("DlyTestCntDfiClkHM",,get_full_name());
      this.DlyTestCntDfiClkHM.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestCntDfiClkHM)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestCntDfiClkHM


class ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestCntRingOsc extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_DlyTestCntRingOsc");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DlyTestCntRingOsc = uvm_reg_field::type_id::create("DlyTestCntRingOsc",,get_full_name());
      this.DlyTestCntRingOsc.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestCntRingOsc)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestCntRingOsc


class ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestSeqHMAC extends uvm_reg;
	rand uvm_reg_field DlyTestSeqHMAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DlyTestSeqHMAC: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_DlyTestSeqHMAC");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DlyTestSeqHMAC = uvm_reg_field::type_id::create("DlyTestSeqHMAC",,get_full_name());
      this.DlyTestSeqHMAC.configure(this, 6, 0, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestSeqHMAC)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestSeqHMAC


class ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCALcdlAddDlySampEn_p0 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_PclkDCALcdlAddDlySampEn_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCALcdlAddDlySampEn_p0 = uvm_reg_field::type_id::create("PclkDCALcdlAddDlySampEn_p0",,get_full_name());
      this.PclkDCALcdlAddDlySampEn_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCALcdlAddDlySampEn_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCALcdlAddDlySampEn_p0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAClkGaterEnAC extends uvm_reg;
	rand uvm_reg_field PclkDCAClkGaterEnAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCAClkGaterEnAC: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_PclkDCAClkGaterEnAC");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCAClkGaterEnAC = uvm_reg_field::type_id::create("PclkDCAClkGaterEnAC",,get_full_name());
      this.PclkDCAClkGaterEnAC.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAClkGaterEnAC)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAClkGaterEnAC


class ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACodeAC0_p0 extends uvm_reg;
	rand uvm_reg_field PclkDCACoarseAC0;
	rand uvm_reg_field PclkDCAFineAC0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACoarseAC0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	   PclkDCAFineAC0: coverpoint {m_data[8:5], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_PclkDCACodeAC0_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACoarseAC0 = uvm_reg_field::type_id::create("PclkDCACoarseAC0",,get_full_name());
      this.PclkDCACoarseAC0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 0);
      this.PclkDCAFineAC0 = uvm_reg_field::type_id::create("PclkDCAFineAC0",,get_full_name());
      this.PclkDCAFineAC0.configure(this, 4, 5, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACodeAC0_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACodeAC0_p0


class ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACodeAC1_p0 extends uvm_reg;
	rand uvm_reg_field PclkDCACoarseAC1;
	rand uvm_reg_field PclkDCAFineAC1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACoarseAC1: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	   PclkDCAFineAC1: coverpoint {m_data[8:5], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC1_p0_PclkDCACodeAC1_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACoarseAC1 = uvm_reg_field::type_id::create("PclkDCACoarseAC1",,get_full_name());
      this.PclkDCACoarseAC1.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 0);
      this.PclkDCAFineAC1 = uvm_reg_field::type_id::create("PclkDCAFineAC1",,get_full_name());
      this.PclkDCAFineAC1.configure(this, 4, 5, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACodeAC1_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACodeAC1_p0


class ral_block_DWC_DDRPHYA_HMAC1_p0 extends uvm_reg_block;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_AnibRcvPtrInitValS0 AnibRcvPtrInitValS0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_AnibRcvPtrInitValS1 AnibRcvPtrInitValS1;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_RxPowerDownAC RxPowerDownAC;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_ACRxClkEn ACRxClkEn;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_CKDllControl CKDllControl;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_MtestMuxSel MtestMuxSel;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_NeverGateACDlyCalValClk NeverGateACDlyCalValClk;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_NeverGateACDlyScaleValClk NeverGateACDlyScaleValClk;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_ACReserved ACReserved;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_ACReservedP_p0 ACReservedP_p0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_HMACParityInvert HMACParityInvert;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_HMLcdlStatusSel HMLcdlStatusSel;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_HMLcdlStatus HMLcdlStatus;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_HMTxLcdlSeed_p0 HMTxLcdlSeed_p0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_HMACLcdlCalDeltaStepEn HMACLcdlCalDeltaStepEn;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_LcdlMonitorCtl_p0 LcdlMonitorCtl_p0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_HMACLcdlCalDeltaMM_p0 HMACLcdlCalDeltaMM_p0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_TxACDcaModeLn0_p0 TxACDcaModeLn0_p0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_TxACDcaModeLn1_p0 TxACDcaModeLn1_p0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_TxModeCtlAC TxModeCtlAC;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_TxSlewAC_p0 TxSlewAC_p0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_TxImpedanceAC_p0 TxImpedanceAC_p0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_TxAcDcaCtrl0 TxAcDcaCtrl0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_TxAcDcaCtrl1 TxAcDcaCtrl1;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_OdtImpedanceAC_p0 OdtImpedanceAC_p0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_ScratchPadHMAC ScratchPadHMAC;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_AcCoreLoopBackMode AcCoreLoopBackMode;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_RxAcAttenCtrlLn0 RxAcAttenCtrlLn0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_RxAcAttenCtrlLn1 RxAcAttenCtrlLn1;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_LcdlTstPhase LcdlTstPhase;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_HardMacroModeSel HardMacroModeSel;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_TxFuncMode TxFuncMode;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_HMReserved0 HMReserved0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_HMReservedP1_p0 HMReservedP1_p0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCATxLcdlPhase_p0 PclkDCATxLcdlPhase_p0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACalSampAC0 PclkDCACalSampAC0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACalSampAC1 PclkDCACalSampAC1;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAResults PclkDCAResults;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_ACXPowerDownLn0 ACXPowerDownLn0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_ACXPowerDownLn1 ACXPowerDownLn1;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAStaticCtrl1AC_p0 PclkDCAStaticCtrl1AC_p0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCASampDelayLCDLAC_p0 PclkDCASampDelayLCDLAC_p0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAStatusSel PclkDCAStatusSel;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAStatusInfo PclkDCAStatusInfo;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACoarseBoundAC PclkDCACoarseBoundAC;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAMiscCtrlAC PclkDCAMiscCtrlAC;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCDOffsetAC0_p0 PclkDCDOffsetAC0_p0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCDOffsetAC1_p0 PclkDCDOffsetAC1_p0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCALcdlCalCtrl PclkDCALcdlCalCtrl;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestCntRingOscSelACX DlyTestCntRingOscSelACX;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestRingSelACX DlyTestRingSelACX;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestCntDfiClkIVHM DlyTestCntDfiClkIVHM;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestCntDfiClkHM DlyTestCntDfiClkHM;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestCntRingOsc DlyTestCntRingOsc;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestSeqHMAC DlyTestSeqHMAC;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCALcdlAddDlySampEn_p0 PclkDCALcdlAddDlySampEn_p0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAClkGaterEnAC PclkDCAClkGaterEnAC;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACodeAC0_p0 PclkDCACodeAC0_p0;
	rand ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACodeAC1_p0 PclkDCACodeAC1_p0;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field AnibRcvPtrInitValS0_AnibRcvPtrInitValS0;
	rand uvm_reg_field AnibRcvPtrInitValS1_AnibRcvPtrInitValS1;
	rand uvm_reg_field RxPowerDownAC_RxPowerDownAC;
	rand uvm_reg_field ACRxClkEn_ACRxClkEn;
	rand uvm_reg_field CKDllControl_CKDllControl;
	rand uvm_reg_field MtestMuxSel_MtestMuxSel;
	rand uvm_reg_field NeverGateACDlyCalValClk_NeverGateACDlyCalValClk;
	rand uvm_reg_field NeverGateACDlyScaleValClk_NeverGateACDlyScaleValClk;
	rand uvm_reg_field ACReserved_ReservedACS;
	rand uvm_reg_field ReservedACS;
	rand uvm_reg_field ACReservedP_p0_ReservedACPS;
	rand uvm_reg_field ReservedACPS;
	rand uvm_reg_field HMACParityInvert_HMACParityInvert;
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
	rand uvm_reg_field HMACLcdlCalDeltaStepEn_TxLcdlCalDeltaStepEn;
	rand uvm_reg_field TxLcdlCalDeltaStepEn;
	rand uvm_reg_field LcdlMonitorCtl_p0_StickyUnlckThrshld;
	rand uvm_reg_field StickyUnlckThrshld;
	rand uvm_reg_field HMACLcdlCalDeltaMM_p0_TxLcdlCalDeltaMM;
	rand uvm_reg_field TxLcdlCalDeltaMM;
	rand uvm_reg_field TxACDcaModeLn0_p0_TxACDcaModeLn0_p0;
	rand uvm_reg_field TxACDcaModeLn1_p0_TxACDcaModeLn1_p0;
	rand uvm_reg_field TxModeCtlAC_TxModeCtlAC;
	rand uvm_reg_field TxSlewAC_p0_TxSlewPUAC;
	rand uvm_reg_field TxSlewPUAC;
	rand uvm_reg_field TxSlewAC_p0_TxSlewPDAC;
	rand uvm_reg_field TxSlewPDAC;
	rand uvm_reg_field TxImpedanceAC_p0_TxStrenCodePUAC;
	rand uvm_reg_field TxStrenCodePUAC;
	rand uvm_reg_field TxImpedanceAC_p0_TxStrenCodePDAC;
	rand uvm_reg_field TxStrenCodePDAC;
	rand uvm_reg_field TxAcDcaCtrl0_TxACDcaCoarse0;
	rand uvm_reg_field TxACDcaCoarse0;
	rand uvm_reg_field TxAcDcaCtrl0_TxACDcaFinePU0;
	rand uvm_reg_field TxACDcaFinePU0;
	rand uvm_reg_field TxAcDcaCtrl0_TxACDcaFinePD0;
	rand uvm_reg_field TxACDcaFinePD0;
	rand uvm_reg_field TxAcDcaCtrl1_TxACDcaCoarse1;
	rand uvm_reg_field TxACDcaCoarse1;
	rand uvm_reg_field TxAcDcaCtrl1_TxACDcaFinePU1;
	rand uvm_reg_field TxACDcaFinePU1;
	rand uvm_reg_field TxAcDcaCtrl1_TxACDcaFinePD1;
	rand uvm_reg_field TxACDcaFinePD1;
	rand uvm_reg_field OdtImpedanceAC_p0_OdtStrenCodePUAC;
	rand uvm_reg_field OdtStrenCodePUAC;
	rand uvm_reg_field OdtImpedanceAC_p0_OdtStrenCodePDAC;
	rand uvm_reg_field OdtStrenCodePDAC;
	rand uvm_reg_field ScratchPadHMAC_ScratchPadHMAC;
	rand uvm_reg_field AcCoreLoopBackMode_AcCoreLoopBackMode;
	rand uvm_reg_field RxAcAttenCtrlLn0_RxAcAttenCtrlLn0;
	rand uvm_reg_field RxAcAttenCtrlLn1_RxAcAttenCtrlLn1;
	rand uvm_reg_field LcdlTstPhase_LcdlTstPhase;
	rand uvm_reg_field HardMacroModeSel_HardMacroModeSel;
	rand uvm_reg_field TxFuncMode_TxFuncMode;
	rand uvm_reg_field HMReserved0_HMReserved0;
	rand uvm_reg_field HMReservedP1_p0_HMReservedP1_p0;
	rand uvm_reg_field PclkDCATxLcdlPhase_p0_PclkDCATxLcdlPhase_p0;
	uvm_reg_field PclkDCACalSampAC0_PclkDCACalSampAC0;
	uvm_reg_field PclkDCACalSampAC1_PclkDCACalSampAC1;
	uvm_reg_field PclkDCAResults_PclkDCADone;
	uvm_reg_field PclkDCADone;
	uvm_reg_field PclkDCAResults_PclkDCASuccessful;
	uvm_reg_field PclkDCASuccessful;
	rand uvm_reg_field ACXPowerDownLn0_AcTxPowerDownLn0;
	rand uvm_reg_field AcTxPowerDownLn0;
	rand uvm_reg_field ACXPowerDownLn1_AcTxPowerDownLn1;
	rand uvm_reg_field AcTxPowerDownLn1;
	rand uvm_reg_field PclkDCAStaticCtrl1AC_p0_PclkDCAInvertSampAC;
	rand uvm_reg_field PclkDCAInvertSampAC;
	rand uvm_reg_field PclkDCAStaticCtrl1AC_p0_PclkDCALcdlEn4pAC;
	rand uvm_reg_field PclkDCALcdlEn4pAC;
	rand uvm_reg_field PclkDCAStaticCtrl1AC_p0_PclkDCDMissionModeDelayAC;
	rand uvm_reg_field PclkDCDMissionModeDelayAC;
	rand uvm_reg_field PclkDCASampDelayLCDLAC_p0_PclkDCASampDelayLCDLAC_p0;
	rand uvm_reg_field PclkDCAStatusSel_PclkDCADebugLaneSel;
	rand uvm_reg_field PclkDCADebugLaneSel;
	rand uvm_reg_field PclkDCAStatusSel_PclkDCADebugInfoSel;
	rand uvm_reg_field PclkDCADebugInfoSel;
	uvm_reg_field PclkDCAStatusInfo_PclkDCAStatusInfo;
	rand uvm_reg_field PclkDCACoarseBoundAC_PclkDCAMaxCoarseAC;
	rand uvm_reg_field PclkDCAMaxCoarseAC;
	rand uvm_reg_field PclkDCACoarseBoundAC_PclkDCAMinCoarseAC;
	rand uvm_reg_field PclkDCAMinCoarseAC;
	rand uvm_reg_field PclkDCAMiscCtrlAC_PclkDCADitherModeAC;
	rand uvm_reg_field PclkDCADitherModeAC;
	rand uvm_reg_field PclkDCAMiscCtrlAC_PclkDCDForceCkEnAC;
	rand uvm_reg_field PclkDCDForceCkEnAC;
	rand uvm_reg_field PclkDCAMiscCtrlAC_PclkDCAReservedAC;
	rand uvm_reg_field PclkDCAReservedAC;
	rand uvm_reg_field PclkDCDOffsetAC0_p0_PclkDCDOffsetAC0_p0;
	rand uvm_reg_field PclkDCDOffsetAC1_p0_PclkDCDOffsetAC1_p0;
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
	rand uvm_reg_field DlyTestCntRingOscSelACX_DlyTestCntRingOscSelACX;
	rand uvm_reg_field DlyTestRingSelACX_DlyTestRingSelACX;
	rand uvm_reg_field DlyTestCntDfiClkIVHM_DlyTestCntDfiClkIVHM;
	uvm_reg_field DlyTestCntDfiClkHM_DlyTestCntDfiClkHM;
	uvm_reg_field DlyTestCntRingOsc_DlyTestCntRingOsc;
	rand uvm_reg_field DlyTestSeqHMAC_DlyTestSeqHMAC;
	rand uvm_reg_field PclkDCALcdlAddDlySampEn_p0_PclkDCALcdlAddDlySampEn_p0;
	rand uvm_reg_field PclkDCAClkGaterEnAC_PclkDCAClkGaterEnAC;
	rand uvm_reg_field PclkDCACodeAC0_p0_PclkDCACoarseAC0;
	rand uvm_reg_field PclkDCACoarseAC0;
	rand uvm_reg_field PclkDCACodeAC0_p0_PclkDCAFineAC0;
	rand uvm_reg_field PclkDCAFineAC0;
	rand uvm_reg_field PclkDCACodeAC1_p0_PclkDCACoarseAC1;
	rand uvm_reg_field PclkDCACoarseAC1;
	rand uvm_reg_field PclkDCACodeAC1_p0_PclkDCAFineAC1;
	rand uvm_reg_field PclkDCAFineAC1;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	AnibRcvPtrInitValS0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h0 };
		option.weight = 1;
	}

	AnibRcvPtrInitValS1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1 };
		option.weight = 1;
	}

	RxPowerDownAC : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5 };
		option.weight = 1;
	}

	ACRxClkEn : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h8 };
		option.weight = 1;
	}

	CKDllControl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB };
		option.weight = 1;
	}

	MtestMuxSel : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1A };
		option.weight = 1;
	}

	NeverGateACDlyCalValClk : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2F };
		option.weight = 1;
	}

	NeverGateACDlyScaleValClk : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3F };
		option.weight = 1;
	}

	ACReserved : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h46 };
		option.weight = 1;
	}

	ACReservedP_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h47 };
		option.weight = 1;
	}

	HMACParityInvert : coverpoint m_offset {
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

	HMACLcdlCalDeltaStepEn : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h65 };
		option.weight = 1;
	}

	LcdlMonitorCtl_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h66 };
		option.weight = 1;
	}

	HMACLcdlCalDeltaMM_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h67 };
		option.weight = 1;
	}

	TxACDcaModeLn0_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h68 };
		option.weight = 1;
	}

	TxACDcaModeLn1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h69 };
		option.weight = 1;
	}

	TxModeCtlAC : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h6A };
		option.weight = 1;
	}

	TxSlewAC_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h6D };
		option.weight = 1;
	}

	TxImpedanceAC_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h70 };
		option.weight = 1;
	}

	TxAcDcaCtrl0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h71 };
		option.weight = 1;
	}

	TxAcDcaCtrl1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h72 };
		option.weight = 1;
	}

	OdtImpedanceAC_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h79 };
		option.weight = 1;
	}

	ScratchPadHMAC : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h7D };
		option.weight = 1;
	}

	AcCoreLoopBackMode : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h80 };
		option.weight = 1;
	}

	RxAcAttenCtrlLn0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h82 };
		option.weight = 1;
	}

	RxAcAttenCtrlLn1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h83 };
		option.weight = 1;
	}

	LcdlTstPhase : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h84 };
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

	PclkDCACalSampAC0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h308 };
		option.weight = 1;
	}

	PclkDCACalSampAC1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h309 };
		option.weight = 1;
	}

	PclkDCAResults : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h30A };
		option.weight = 1;
	}

	ACXPowerDownLn0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3D6 };
		option.weight = 1;
	}

	ACXPowerDownLn1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3D7 };
		option.weight = 1;
	}

	PclkDCAStaticCtrl1AC_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h503 };
		option.weight = 1;
	}

	PclkDCASampDelayLCDLAC_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h50A };
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

	PclkDCACoarseBoundAC : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h51C };
		option.weight = 1;
	}

	PclkDCAMiscCtrlAC : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h51E };
		option.weight = 1;
	}

	PclkDCDOffsetAC0_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h560 };
		option.weight = 1;
	}

	PclkDCDOffsetAC1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h561 };
		option.weight = 1;
	}

	PclkDCALcdlCalCtrl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h591 };
		option.weight = 1;
	}

	DlyTestCntRingOscSelACX : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h592 };
		option.weight = 1;
	}

	DlyTestRingSelACX : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5D2 };
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

	DlyTestSeqHMAC : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5DF };
		option.weight = 1;
	}

	PclkDCALcdlAddDlySampEn_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5E3 };
		option.weight = 1;
	}

	PclkDCAClkGaterEnAC : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h61E };
		option.weight = 1;
	}

	PclkDCACodeAC0_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h660 };
		option.weight = 1;
	}

	PclkDCACodeAC1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h661 };
		option.weight = 1;
	}
endgroup
	function new(string name = "DWC_DDRPHYA_HMAC1_p0");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.AnibRcvPtrInitValS0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_AnibRcvPtrInitValS0::type_id::create("AnibRcvPtrInitValS0",,get_full_name());
      if(this.AnibRcvPtrInitValS0.has_coverage(UVM_CVR_ALL))
      	this.AnibRcvPtrInitValS0.cg_bits.option.name = {get_name(), ".", "AnibRcvPtrInitValS0_bits"};
      this.AnibRcvPtrInitValS0.configure(this, null, "");
      this.AnibRcvPtrInitValS0.build();
      this.default_map.add_reg(this.AnibRcvPtrInitValS0, `UVM_REG_ADDR_WIDTH'h0, "RW", 0);
		this.AnibRcvPtrInitValS0_AnibRcvPtrInitValS0 = this.AnibRcvPtrInitValS0.AnibRcvPtrInitValS0;
      this.AnibRcvPtrInitValS1 = ral_reg_DWC_DDRPHYA_HMAC1_p0_AnibRcvPtrInitValS1::type_id::create("AnibRcvPtrInitValS1",,get_full_name());
      if(this.AnibRcvPtrInitValS1.has_coverage(UVM_CVR_ALL))
      	this.AnibRcvPtrInitValS1.cg_bits.option.name = {get_name(), ".", "AnibRcvPtrInitValS1_bits"};
      this.AnibRcvPtrInitValS1.configure(this, null, "");
      this.AnibRcvPtrInitValS1.build();
      this.default_map.add_reg(this.AnibRcvPtrInitValS1, `UVM_REG_ADDR_WIDTH'h1, "RW", 0);
		this.AnibRcvPtrInitValS1_AnibRcvPtrInitValS1 = this.AnibRcvPtrInitValS1.AnibRcvPtrInitValS1;
      this.RxPowerDownAC = ral_reg_DWC_DDRPHYA_HMAC1_p0_RxPowerDownAC::type_id::create("RxPowerDownAC",,get_full_name());
      if(this.RxPowerDownAC.has_coverage(UVM_CVR_ALL))
      	this.RxPowerDownAC.cg_bits.option.name = {get_name(), ".", "RxPowerDownAC_bits"};
      this.RxPowerDownAC.configure(this, null, "");
      this.RxPowerDownAC.build();
      this.default_map.add_reg(this.RxPowerDownAC, `UVM_REG_ADDR_WIDTH'h5, "RW", 0);
		this.RxPowerDownAC_RxPowerDownAC = this.RxPowerDownAC.RxPowerDownAC;
      this.ACRxClkEn = ral_reg_DWC_DDRPHYA_HMAC1_p0_ACRxClkEn::type_id::create("ACRxClkEn",,get_full_name());
      if(this.ACRxClkEn.has_coverage(UVM_CVR_ALL))
      	this.ACRxClkEn.cg_bits.option.name = {get_name(), ".", "ACRxClkEn_bits"};
      this.ACRxClkEn.configure(this, null, "");
      this.ACRxClkEn.build();
      this.default_map.add_reg(this.ACRxClkEn, `UVM_REG_ADDR_WIDTH'h8, "RW", 0);
		this.ACRxClkEn_ACRxClkEn = this.ACRxClkEn.ACRxClkEn;
      this.CKDllControl = ral_reg_DWC_DDRPHYA_HMAC1_p0_CKDllControl::type_id::create("CKDllControl",,get_full_name());
      if(this.CKDllControl.has_coverage(UVM_CVR_ALL))
      	this.CKDllControl.cg_bits.option.name = {get_name(), ".", "CKDllControl_bits"};
      this.CKDllControl.configure(this, null, "");
      this.CKDllControl.build();
      this.default_map.add_reg(this.CKDllControl, `UVM_REG_ADDR_WIDTH'hB, "RW", 0);
		this.CKDllControl_CKDllControl = this.CKDllControl.CKDllControl;
      this.MtestMuxSel = ral_reg_DWC_DDRPHYA_HMAC1_p0_MtestMuxSel::type_id::create("MtestMuxSel",,get_full_name());
      if(this.MtestMuxSel.has_coverage(UVM_CVR_ALL))
      	this.MtestMuxSel.cg_bits.option.name = {get_name(), ".", "MtestMuxSel_bits"};
      this.MtestMuxSel.configure(this, null, "");
      this.MtestMuxSel.build();
      this.default_map.add_reg(this.MtestMuxSel, `UVM_REG_ADDR_WIDTH'h1A, "RW", 0);
		this.MtestMuxSel_MtestMuxSel = this.MtestMuxSel.MtestMuxSel;
      this.NeverGateACDlyCalValClk = ral_reg_DWC_DDRPHYA_HMAC1_p0_NeverGateACDlyCalValClk::type_id::create("NeverGateACDlyCalValClk",,get_full_name());
      if(this.NeverGateACDlyCalValClk.has_coverage(UVM_CVR_ALL))
      	this.NeverGateACDlyCalValClk.cg_bits.option.name = {get_name(), ".", "NeverGateACDlyCalValClk_bits"};
      this.NeverGateACDlyCalValClk.configure(this, null, "");
      this.NeverGateACDlyCalValClk.build();
      this.default_map.add_reg(this.NeverGateACDlyCalValClk, `UVM_REG_ADDR_WIDTH'h2F, "RW", 0);
		this.NeverGateACDlyCalValClk_NeverGateACDlyCalValClk = this.NeverGateACDlyCalValClk.NeverGateACDlyCalValClk;
      this.NeverGateACDlyScaleValClk = ral_reg_DWC_DDRPHYA_HMAC1_p0_NeverGateACDlyScaleValClk::type_id::create("NeverGateACDlyScaleValClk",,get_full_name());
      if(this.NeverGateACDlyScaleValClk.has_coverage(UVM_CVR_ALL))
      	this.NeverGateACDlyScaleValClk.cg_bits.option.name = {get_name(), ".", "NeverGateACDlyScaleValClk_bits"};
      this.NeverGateACDlyScaleValClk.configure(this, null, "");
      this.NeverGateACDlyScaleValClk.build();
      this.default_map.add_reg(this.NeverGateACDlyScaleValClk, `UVM_REG_ADDR_WIDTH'h3F, "RW", 0);
		this.NeverGateACDlyScaleValClk_NeverGateACDlyScaleValClk = this.NeverGateACDlyScaleValClk.NeverGateACDlyScaleValClk;
      this.ACReserved = ral_reg_DWC_DDRPHYA_HMAC1_p0_ACReserved::type_id::create("ACReserved",,get_full_name());
      if(this.ACReserved.has_coverage(UVM_CVR_ALL))
      	this.ACReserved.cg_bits.option.name = {get_name(), ".", "ACReserved_bits"};
      this.ACReserved.configure(this, null, "");
      this.ACReserved.build();
      this.default_map.add_reg(this.ACReserved, `UVM_REG_ADDR_WIDTH'h46, "RW", 0);
		this.ACReserved_ReservedACS = this.ACReserved.ReservedACS;
		this.ReservedACS = this.ACReserved.ReservedACS;
      this.ACReservedP_p0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_ACReservedP_p0::type_id::create("ACReservedP_p0",,get_full_name());
      if(this.ACReservedP_p0.has_coverage(UVM_CVR_ALL))
      	this.ACReservedP_p0.cg_bits.option.name = {get_name(), ".", "ACReservedP_p0_bits"};
      this.ACReservedP_p0.configure(this, null, "");
      this.ACReservedP_p0.build();
      this.default_map.add_reg(this.ACReservedP_p0, `UVM_REG_ADDR_WIDTH'h47, "RW", 0);
		this.ACReservedP_p0_ReservedACPS = this.ACReservedP_p0.ReservedACPS;
		this.ReservedACPS = this.ACReservedP_p0.ReservedACPS;
      this.HMACParityInvert = ral_reg_DWC_DDRPHYA_HMAC1_p0_HMACParityInvert::type_id::create("HMACParityInvert",,get_full_name());
      if(this.HMACParityInvert.has_coverage(UVM_CVR_ALL))
      	this.HMACParityInvert.cg_bits.option.name = {get_name(), ".", "HMACParityInvert_bits"};
      this.HMACParityInvert.configure(this, null, "");
      this.HMACParityInvert.build();
      this.default_map.add_reg(this.HMACParityInvert, `UVM_REG_ADDR_WIDTH'h4D, "RW", 0);
		this.HMACParityInvert_HMACParityInvert = this.HMACParityInvert.HMACParityInvert;
      this.HMLcdlStatusSel = ral_reg_DWC_DDRPHYA_HMAC1_p0_HMLcdlStatusSel::type_id::create("HMLcdlStatusSel",,get_full_name());
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
      this.HMLcdlStatus = ral_reg_DWC_DDRPHYA_HMAC1_p0_HMLcdlStatus::type_id::create("HMLcdlStatus",,get_full_name());
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
      this.HMTxLcdlSeed_p0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_HMTxLcdlSeed_p0::type_id::create("HMTxLcdlSeed_p0",,get_full_name());
      if(this.HMTxLcdlSeed_p0.has_coverage(UVM_CVR_ALL))
      	this.HMTxLcdlSeed_p0.cg_bits.option.name = {get_name(), ".", "HMTxLcdlSeed_p0_bits"};
      this.HMTxLcdlSeed_p0.configure(this, null, "");
      this.HMTxLcdlSeed_p0.build();
      this.default_map.add_reg(this.HMTxLcdlSeed_p0, `UVM_REG_ADDR_WIDTH'h63, "RW", 0);
		this.HMTxLcdlSeed_p0_HMTxLcdlSeed_p0 = this.HMTxLcdlSeed_p0.HMTxLcdlSeed_p0;
      this.HMACLcdlCalDeltaStepEn = ral_reg_DWC_DDRPHYA_HMAC1_p0_HMACLcdlCalDeltaStepEn::type_id::create("HMACLcdlCalDeltaStepEn",,get_full_name());
      if(this.HMACLcdlCalDeltaStepEn.has_coverage(UVM_CVR_ALL))
      	this.HMACLcdlCalDeltaStepEn.cg_bits.option.name = {get_name(), ".", "HMACLcdlCalDeltaStepEn_bits"};
      this.HMACLcdlCalDeltaStepEn.configure(this, null, "");
      this.HMACLcdlCalDeltaStepEn.build();
      this.default_map.add_reg(this.HMACLcdlCalDeltaStepEn, `UVM_REG_ADDR_WIDTH'h65, "RW", 0);
		this.HMACLcdlCalDeltaStepEn_TxLcdlCalDeltaStepEn = this.HMACLcdlCalDeltaStepEn.TxLcdlCalDeltaStepEn;
		this.TxLcdlCalDeltaStepEn = this.HMACLcdlCalDeltaStepEn.TxLcdlCalDeltaStepEn;
      this.LcdlMonitorCtl_p0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_LcdlMonitorCtl_p0::type_id::create("LcdlMonitorCtl_p0",,get_full_name());
      if(this.LcdlMonitorCtl_p0.has_coverage(UVM_CVR_ALL))
      	this.LcdlMonitorCtl_p0.cg_bits.option.name = {get_name(), ".", "LcdlMonitorCtl_p0_bits"};
      this.LcdlMonitorCtl_p0.configure(this, null, "");
      this.LcdlMonitorCtl_p0.build();
      this.default_map.add_reg(this.LcdlMonitorCtl_p0, `UVM_REG_ADDR_WIDTH'h66, "RW", 0);
		this.LcdlMonitorCtl_p0_StickyUnlckThrshld = this.LcdlMonitorCtl_p0.StickyUnlckThrshld;
		this.StickyUnlckThrshld = this.LcdlMonitorCtl_p0.StickyUnlckThrshld;
      this.HMACLcdlCalDeltaMM_p0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_HMACLcdlCalDeltaMM_p0::type_id::create("HMACLcdlCalDeltaMM_p0",,get_full_name());
      if(this.HMACLcdlCalDeltaMM_p0.has_coverage(UVM_CVR_ALL))
      	this.HMACLcdlCalDeltaMM_p0.cg_bits.option.name = {get_name(), ".", "HMACLcdlCalDeltaMM_p0_bits"};
      this.HMACLcdlCalDeltaMM_p0.configure(this, null, "");
      this.HMACLcdlCalDeltaMM_p0.build();
      this.default_map.add_reg(this.HMACLcdlCalDeltaMM_p0, `UVM_REG_ADDR_WIDTH'h67, "RW", 0);
		this.HMACLcdlCalDeltaMM_p0_TxLcdlCalDeltaMM = this.HMACLcdlCalDeltaMM_p0.TxLcdlCalDeltaMM;
		this.TxLcdlCalDeltaMM = this.HMACLcdlCalDeltaMM_p0.TxLcdlCalDeltaMM;
      this.TxACDcaModeLn0_p0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_TxACDcaModeLn0_p0::type_id::create("TxACDcaModeLn0_p0",,get_full_name());
      if(this.TxACDcaModeLn0_p0.has_coverage(UVM_CVR_ALL))
      	this.TxACDcaModeLn0_p0.cg_bits.option.name = {get_name(), ".", "TxACDcaModeLn0_p0_bits"};
      this.TxACDcaModeLn0_p0.configure(this, null, "");
      this.TxACDcaModeLn0_p0.build();
      this.default_map.add_reg(this.TxACDcaModeLn0_p0, `UVM_REG_ADDR_WIDTH'h68, "RW", 0);
		this.TxACDcaModeLn0_p0_TxACDcaModeLn0_p0 = this.TxACDcaModeLn0_p0.TxACDcaModeLn0_p0;
      this.TxACDcaModeLn1_p0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_TxACDcaModeLn1_p0::type_id::create("TxACDcaModeLn1_p0",,get_full_name());
      if(this.TxACDcaModeLn1_p0.has_coverage(UVM_CVR_ALL))
      	this.TxACDcaModeLn1_p0.cg_bits.option.name = {get_name(), ".", "TxACDcaModeLn1_p0_bits"};
      this.TxACDcaModeLn1_p0.configure(this, null, "");
      this.TxACDcaModeLn1_p0.build();
      this.default_map.add_reg(this.TxACDcaModeLn1_p0, `UVM_REG_ADDR_WIDTH'h69, "RW", 0);
		this.TxACDcaModeLn1_p0_TxACDcaModeLn1_p0 = this.TxACDcaModeLn1_p0.TxACDcaModeLn1_p0;
      this.TxModeCtlAC = ral_reg_DWC_DDRPHYA_HMAC1_p0_TxModeCtlAC::type_id::create("TxModeCtlAC",,get_full_name());
      if(this.TxModeCtlAC.has_coverage(UVM_CVR_ALL))
      	this.TxModeCtlAC.cg_bits.option.name = {get_name(), ".", "TxModeCtlAC_bits"};
      this.TxModeCtlAC.configure(this, null, "");
      this.TxModeCtlAC.build();
      this.default_map.add_reg(this.TxModeCtlAC, `UVM_REG_ADDR_WIDTH'h6A, "RW", 0);
		this.TxModeCtlAC_TxModeCtlAC = this.TxModeCtlAC.TxModeCtlAC;
      this.TxSlewAC_p0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_TxSlewAC_p0::type_id::create("TxSlewAC_p0",,get_full_name());
      if(this.TxSlewAC_p0.has_coverage(UVM_CVR_ALL))
      	this.TxSlewAC_p0.cg_bits.option.name = {get_name(), ".", "TxSlewAC_p0_bits"};
      this.TxSlewAC_p0.configure(this, null, "");
      this.TxSlewAC_p0.build();
      this.default_map.add_reg(this.TxSlewAC_p0, `UVM_REG_ADDR_WIDTH'h6D, "RW", 0);
		this.TxSlewAC_p0_TxSlewPUAC = this.TxSlewAC_p0.TxSlewPUAC;
		this.TxSlewPUAC = this.TxSlewAC_p0.TxSlewPUAC;
		this.TxSlewAC_p0_TxSlewPDAC = this.TxSlewAC_p0.TxSlewPDAC;
		this.TxSlewPDAC = this.TxSlewAC_p0.TxSlewPDAC;
      this.TxImpedanceAC_p0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_TxImpedanceAC_p0::type_id::create("TxImpedanceAC_p0",,get_full_name());
      if(this.TxImpedanceAC_p0.has_coverage(UVM_CVR_ALL))
      	this.TxImpedanceAC_p0.cg_bits.option.name = {get_name(), ".", "TxImpedanceAC_p0_bits"};
      this.TxImpedanceAC_p0.configure(this, null, "");
      this.TxImpedanceAC_p0.build();
      this.default_map.add_reg(this.TxImpedanceAC_p0, `UVM_REG_ADDR_WIDTH'h70, "RW", 0);
		this.TxImpedanceAC_p0_TxStrenCodePUAC = this.TxImpedanceAC_p0.TxStrenCodePUAC;
		this.TxStrenCodePUAC = this.TxImpedanceAC_p0.TxStrenCodePUAC;
		this.TxImpedanceAC_p0_TxStrenCodePDAC = this.TxImpedanceAC_p0.TxStrenCodePDAC;
		this.TxStrenCodePDAC = this.TxImpedanceAC_p0.TxStrenCodePDAC;
      this.TxAcDcaCtrl0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_TxAcDcaCtrl0::type_id::create("TxAcDcaCtrl0",,get_full_name());
      if(this.TxAcDcaCtrl0.has_coverage(UVM_CVR_ALL))
      	this.TxAcDcaCtrl0.cg_bits.option.name = {get_name(), ".", "TxAcDcaCtrl0_bits"};
      this.TxAcDcaCtrl0.configure(this, null, "");
      this.TxAcDcaCtrl0.build();
      this.default_map.add_reg(this.TxAcDcaCtrl0, `UVM_REG_ADDR_WIDTH'h71, "RW", 0);
		this.TxAcDcaCtrl0_TxACDcaCoarse0 = this.TxAcDcaCtrl0.TxACDcaCoarse0;
		this.TxACDcaCoarse0 = this.TxAcDcaCtrl0.TxACDcaCoarse0;
		this.TxAcDcaCtrl0_TxACDcaFinePU0 = this.TxAcDcaCtrl0.TxACDcaFinePU0;
		this.TxACDcaFinePU0 = this.TxAcDcaCtrl0.TxACDcaFinePU0;
		this.TxAcDcaCtrl0_TxACDcaFinePD0 = this.TxAcDcaCtrl0.TxACDcaFinePD0;
		this.TxACDcaFinePD0 = this.TxAcDcaCtrl0.TxACDcaFinePD0;
      this.TxAcDcaCtrl1 = ral_reg_DWC_DDRPHYA_HMAC1_p0_TxAcDcaCtrl1::type_id::create("TxAcDcaCtrl1",,get_full_name());
      if(this.TxAcDcaCtrl1.has_coverage(UVM_CVR_ALL))
      	this.TxAcDcaCtrl1.cg_bits.option.name = {get_name(), ".", "TxAcDcaCtrl1_bits"};
      this.TxAcDcaCtrl1.configure(this, null, "");
      this.TxAcDcaCtrl1.build();
      this.default_map.add_reg(this.TxAcDcaCtrl1, `UVM_REG_ADDR_WIDTH'h72, "RW", 0);
		this.TxAcDcaCtrl1_TxACDcaCoarse1 = this.TxAcDcaCtrl1.TxACDcaCoarse1;
		this.TxACDcaCoarse1 = this.TxAcDcaCtrl1.TxACDcaCoarse1;
		this.TxAcDcaCtrl1_TxACDcaFinePU1 = this.TxAcDcaCtrl1.TxACDcaFinePU1;
		this.TxACDcaFinePU1 = this.TxAcDcaCtrl1.TxACDcaFinePU1;
		this.TxAcDcaCtrl1_TxACDcaFinePD1 = this.TxAcDcaCtrl1.TxACDcaFinePD1;
		this.TxACDcaFinePD1 = this.TxAcDcaCtrl1.TxACDcaFinePD1;
      this.OdtImpedanceAC_p0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_OdtImpedanceAC_p0::type_id::create("OdtImpedanceAC_p0",,get_full_name());
      if(this.OdtImpedanceAC_p0.has_coverage(UVM_CVR_ALL))
      	this.OdtImpedanceAC_p0.cg_bits.option.name = {get_name(), ".", "OdtImpedanceAC_p0_bits"};
      this.OdtImpedanceAC_p0.configure(this, null, "");
      this.OdtImpedanceAC_p0.build();
      this.default_map.add_reg(this.OdtImpedanceAC_p0, `UVM_REG_ADDR_WIDTH'h79, "RW", 0);
		this.OdtImpedanceAC_p0_OdtStrenCodePUAC = this.OdtImpedanceAC_p0.OdtStrenCodePUAC;
		this.OdtStrenCodePUAC = this.OdtImpedanceAC_p0.OdtStrenCodePUAC;
		this.OdtImpedanceAC_p0_OdtStrenCodePDAC = this.OdtImpedanceAC_p0.OdtStrenCodePDAC;
		this.OdtStrenCodePDAC = this.OdtImpedanceAC_p0.OdtStrenCodePDAC;
      this.ScratchPadHMAC = ral_reg_DWC_DDRPHYA_HMAC1_p0_ScratchPadHMAC::type_id::create("ScratchPadHMAC",,get_full_name());
      if(this.ScratchPadHMAC.has_coverage(UVM_CVR_ALL))
      	this.ScratchPadHMAC.cg_bits.option.name = {get_name(), ".", "ScratchPadHMAC_bits"};
      this.ScratchPadHMAC.configure(this, null, "");
      this.ScratchPadHMAC.build();
      this.default_map.add_reg(this.ScratchPadHMAC, `UVM_REG_ADDR_WIDTH'h7D, "RW", 0);
		this.ScratchPadHMAC_ScratchPadHMAC = this.ScratchPadHMAC.ScratchPadHMAC;
      this.AcCoreLoopBackMode = ral_reg_DWC_DDRPHYA_HMAC1_p0_AcCoreLoopBackMode::type_id::create("AcCoreLoopBackMode",,get_full_name());
      if(this.AcCoreLoopBackMode.has_coverage(UVM_CVR_ALL))
      	this.AcCoreLoopBackMode.cg_bits.option.name = {get_name(), ".", "AcCoreLoopBackMode_bits"};
      this.AcCoreLoopBackMode.configure(this, null, "");
      this.AcCoreLoopBackMode.build();
      this.default_map.add_reg(this.AcCoreLoopBackMode, `UVM_REG_ADDR_WIDTH'h80, "RW", 0);
		this.AcCoreLoopBackMode_AcCoreLoopBackMode = this.AcCoreLoopBackMode.AcCoreLoopBackMode;
      this.RxAcAttenCtrlLn0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_RxAcAttenCtrlLn0::type_id::create("RxAcAttenCtrlLn0",,get_full_name());
      if(this.RxAcAttenCtrlLn0.has_coverage(UVM_CVR_ALL))
      	this.RxAcAttenCtrlLn0.cg_bits.option.name = {get_name(), ".", "RxAcAttenCtrlLn0_bits"};
      this.RxAcAttenCtrlLn0.configure(this, null, "");
      this.RxAcAttenCtrlLn0.build();
      this.default_map.add_reg(this.RxAcAttenCtrlLn0, `UVM_REG_ADDR_WIDTH'h82, "RW", 0);
		this.RxAcAttenCtrlLn0_RxAcAttenCtrlLn0 = this.RxAcAttenCtrlLn0.RxAcAttenCtrlLn0;
      this.RxAcAttenCtrlLn1 = ral_reg_DWC_DDRPHYA_HMAC1_p0_RxAcAttenCtrlLn1::type_id::create("RxAcAttenCtrlLn1",,get_full_name());
      if(this.RxAcAttenCtrlLn1.has_coverage(UVM_CVR_ALL))
      	this.RxAcAttenCtrlLn1.cg_bits.option.name = {get_name(), ".", "RxAcAttenCtrlLn1_bits"};
      this.RxAcAttenCtrlLn1.configure(this, null, "");
      this.RxAcAttenCtrlLn1.build();
      this.default_map.add_reg(this.RxAcAttenCtrlLn1, `UVM_REG_ADDR_WIDTH'h83, "RW", 0);
		this.RxAcAttenCtrlLn1_RxAcAttenCtrlLn1 = this.RxAcAttenCtrlLn1.RxAcAttenCtrlLn1;
      this.LcdlTstPhase = ral_reg_DWC_DDRPHYA_HMAC1_p0_LcdlTstPhase::type_id::create("LcdlTstPhase",,get_full_name());
      if(this.LcdlTstPhase.has_coverage(UVM_CVR_ALL))
      	this.LcdlTstPhase.cg_bits.option.name = {get_name(), ".", "LcdlTstPhase_bits"};
      this.LcdlTstPhase.configure(this, null, "");
      this.LcdlTstPhase.build();
      this.default_map.add_reg(this.LcdlTstPhase, `UVM_REG_ADDR_WIDTH'h84, "RW", 0);
		this.LcdlTstPhase_LcdlTstPhase = this.LcdlTstPhase.LcdlTstPhase;
      this.HardMacroModeSel = ral_reg_DWC_DDRPHYA_HMAC1_p0_HardMacroModeSel::type_id::create("HardMacroModeSel",,get_full_name());
      if(this.HardMacroModeSel.has_coverage(UVM_CVR_ALL))
      	this.HardMacroModeSel.cg_bits.option.name = {get_name(), ".", "HardMacroModeSel_bits"};
      this.HardMacroModeSel.configure(this, null, "");
      this.HardMacroModeSel.build();
      this.default_map.add_reg(this.HardMacroModeSel, `UVM_REG_ADDR_WIDTH'hF6, "RW", 0);
		this.HardMacroModeSel_HardMacroModeSel = this.HardMacroModeSel.HardMacroModeSel;
      this.TxFuncMode = ral_reg_DWC_DDRPHYA_HMAC1_p0_TxFuncMode::type_id::create("TxFuncMode",,get_full_name());
      if(this.TxFuncMode.has_coverage(UVM_CVR_ALL))
      	this.TxFuncMode.cg_bits.option.name = {get_name(), ".", "TxFuncMode_bits"};
      this.TxFuncMode.configure(this, null, "");
      this.TxFuncMode.build();
      this.default_map.add_reg(this.TxFuncMode, `UVM_REG_ADDR_WIDTH'hF8, "RW", 0);
		this.TxFuncMode_TxFuncMode = this.TxFuncMode.TxFuncMode;
      this.HMReserved0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_HMReserved0::type_id::create("HMReserved0",,get_full_name());
      if(this.HMReserved0.has_coverage(UVM_CVR_ALL))
      	this.HMReserved0.cg_bits.option.name = {get_name(), ".", "HMReserved0_bits"};
      this.HMReserved0.configure(this, null, "");
      this.HMReserved0.build();
      this.default_map.add_reg(this.HMReserved0, `UVM_REG_ADDR_WIDTH'hFE, "RW", 0);
		this.HMReserved0_HMReserved0 = this.HMReserved0.HMReserved0;
      this.HMReservedP1_p0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_HMReservedP1_p0::type_id::create("HMReservedP1_p0",,get_full_name());
      if(this.HMReservedP1_p0.has_coverage(UVM_CVR_ALL))
      	this.HMReservedP1_p0.cg_bits.option.name = {get_name(), ".", "HMReservedP1_p0_bits"};
      this.HMReservedP1_p0.configure(this, null, "");
      this.HMReservedP1_p0.build();
      this.default_map.add_reg(this.HMReservedP1_p0, `UVM_REG_ADDR_WIDTH'hFF, "RW", 0);
		this.HMReservedP1_p0_HMReservedP1_p0 = this.HMReservedP1_p0.HMReservedP1_p0;
      this.PclkDCATxLcdlPhase_p0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCATxLcdlPhase_p0::type_id::create("PclkDCATxLcdlPhase_p0",,get_full_name());
      if(this.PclkDCATxLcdlPhase_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCATxLcdlPhase_p0.cg_bits.option.name = {get_name(), ".", "PclkDCATxLcdlPhase_p0_bits"};
      this.PclkDCATxLcdlPhase_p0.configure(this, null, "");
      this.PclkDCATxLcdlPhase_p0.build();
      this.default_map.add_reg(this.PclkDCATxLcdlPhase_p0, `UVM_REG_ADDR_WIDTH'h110, "RW", 0);
		this.PclkDCATxLcdlPhase_p0_PclkDCATxLcdlPhase_p0 = this.PclkDCATxLcdlPhase_p0.PclkDCATxLcdlPhase_p0;
      this.PclkDCACalSampAC0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACalSampAC0::type_id::create("PclkDCACalSampAC0",,get_full_name());
      if(this.PclkDCACalSampAC0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACalSampAC0.cg_bits.option.name = {get_name(), ".", "PclkDCACalSampAC0_bits"};
      this.PclkDCACalSampAC0.configure(this, null, "");
      this.PclkDCACalSampAC0.build();
      this.default_map.add_reg(this.PclkDCACalSampAC0, `UVM_REG_ADDR_WIDTH'h308, "RO", 0);
		this.PclkDCACalSampAC0_PclkDCACalSampAC0 = this.PclkDCACalSampAC0.PclkDCACalSampAC0;
      this.PclkDCACalSampAC1 = ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACalSampAC1::type_id::create("PclkDCACalSampAC1",,get_full_name());
      if(this.PclkDCACalSampAC1.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACalSampAC1.cg_bits.option.name = {get_name(), ".", "PclkDCACalSampAC1_bits"};
      this.PclkDCACalSampAC1.configure(this, null, "");
      this.PclkDCACalSampAC1.build();
      this.default_map.add_reg(this.PclkDCACalSampAC1, `UVM_REG_ADDR_WIDTH'h309, "RO", 0);
		this.PclkDCACalSampAC1_PclkDCACalSampAC1 = this.PclkDCACalSampAC1.PclkDCACalSampAC1;
      this.PclkDCAResults = ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAResults::type_id::create("PclkDCAResults",,get_full_name());
      if(this.PclkDCAResults.has_coverage(UVM_CVR_ALL))
      	this.PclkDCAResults.cg_bits.option.name = {get_name(), ".", "PclkDCAResults_bits"};
      this.PclkDCAResults.configure(this, null, "");
      this.PclkDCAResults.build();
      this.default_map.add_reg(this.PclkDCAResults, `UVM_REG_ADDR_WIDTH'h30A, "RO", 0);
		this.PclkDCAResults_PclkDCADone = this.PclkDCAResults.PclkDCADone;
		this.PclkDCADone = this.PclkDCAResults.PclkDCADone;
		this.PclkDCAResults_PclkDCASuccessful = this.PclkDCAResults.PclkDCASuccessful;
		this.PclkDCASuccessful = this.PclkDCAResults.PclkDCASuccessful;
      this.ACXPowerDownLn0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_ACXPowerDownLn0::type_id::create("ACXPowerDownLn0",,get_full_name());
      if(this.ACXPowerDownLn0.has_coverage(UVM_CVR_ALL))
      	this.ACXPowerDownLn0.cg_bits.option.name = {get_name(), ".", "ACXPowerDownLn0_bits"};
      this.ACXPowerDownLn0.configure(this, null, "");
      this.ACXPowerDownLn0.build();
      this.default_map.add_reg(this.ACXPowerDownLn0, `UVM_REG_ADDR_WIDTH'h3D6, "RW", 0);
		this.ACXPowerDownLn0_AcTxPowerDownLn0 = this.ACXPowerDownLn0.AcTxPowerDownLn0;
		this.AcTxPowerDownLn0 = this.ACXPowerDownLn0.AcTxPowerDownLn0;
      this.ACXPowerDownLn1 = ral_reg_DWC_DDRPHYA_HMAC1_p0_ACXPowerDownLn1::type_id::create("ACXPowerDownLn1",,get_full_name());
      if(this.ACXPowerDownLn1.has_coverage(UVM_CVR_ALL))
      	this.ACXPowerDownLn1.cg_bits.option.name = {get_name(), ".", "ACXPowerDownLn1_bits"};
      this.ACXPowerDownLn1.configure(this, null, "");
      this.ACXPowerDownLn1.build();
      this.default_map.add_reg(this.ACXPowerDownLn1, `UVM_REG_ADDR_WIDTH'h3D7, "RW", 0);
		this.ACXPowerDownLn1_AcTxPowerDownLn1 = this.ACXPowerDownLn1.AcTxPowerDownLn1;
		this.AcTxPowerDownLn1 = this.ACXPowerDownLn1.AcTxPowerDownLn1;
      this.PclkDCAStaticCtrl1AC_p0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAStaticCtrl1AC_p0::type_id::create("PclkDCAStaticCtrl1AC_p0",,get_full_name());
      if(this.PclkDCAStaticCtrl1AC_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCAStaticCtrl1AC_p0.cg_bits.option.name = {get_name(), ".", "PclkDCAStaticCtrl1AC_p0_bits"};
      this.PclkDCAStaticCtrl1AC_p0.configure(this, null, "");
      this.PclkDCAStaticCtrl1AC_p0.build();
      this.default_map.add_reg(this.PclkDCAStaticCtrl1AC_p0, `UVM_REG_ADDR_WIDTH'h503, "RW", 0);
		this.PclkDCAStaticCtrl1AC_p0_PclkDCAInvertSampAC = this.PclkDCAStaticCtrl1AC_p0.PclkDCAInvertSampAC;
		this.PclkDCAInvertSampAC = this.PclkDCAStaticCtrl1AC_p0.PclkDCAInvertSampAC;
		this.PclkDCAStaticCtrl1AC_p0_PclkDCALcdlEn4pAC = this.PclkDCAStaticCtrl1AC_p0.PclkDCALcdlEn4pAC;
		this.PclkDCALcdlEn4pAC = this.PclkDCAStaticCtrl1AC_p0.PclkDCALcdlEn4pAC;
		this.PclkDCAStaticCtrl1AC_p0_PclkDCDMissionModeDelayAC = this.PclkDCAStaticCtrl1AC_p0.PclkDCDMissionModeDelayAC;
		this.PclkDCDMissionModeDelayAC = this.PclkDCAStaticCtrl1AC_p0.PclkDCDMissionModeDelayAC;
      this.PclkDCASampDelayLCDLAC_p0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCASampDelayLCDLAC_p0::type_id::create("PclkDCASampDelayLCDLAC_p0",,get_full_name());
      if(this.PclkDCASampDelayLCDLAC_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCASampDelayLCDLAC_p0.cg_bits.option.name = {get_name(), ".", "PclkDCASampDelayLCDLAC_p0_bits"};
      this.PclkDCASampDelayLCDLAC_p0.configure(this, null, "");
      this.PclkDCASampDelayLCDLAC_p0.build();
      this.default_map.add_reg(this.PclkDCASampDelayLCDLAC_p0, `UVM_REG_ADDR_WIDTH'h50A, "RW", 0);
		this.PclkDCASampDelayLCDLAC_p0_PclkDCASampDelayLCDLAC_p0 = this.PclkDCASampDelayLCDLAC_p0.PclkDCASampDelayLCDLAC_p0;
      this.PclkDCAStatusSel = ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAStatusSel::type_id::create("PclkDCAStatusSel",,get_full_name());
      if(this.PclkDCAStatusSel.has_coverage(UVM_CVR_ALL))
      	this.PclkDCAStatusSel.cg_bits.option.name = {get_name(), ".", "PclkDCAStatusSel_bits"};
      this.PclkDCAStatusSel.configure(this, null, "");
      this.PclkDCAStatusSel.build();
      this.default_map.add_reg(this.PclkDCAStatusSel, `UVM_REG_ADDR_WIDTH'h511, "RW", 0);
		this.PclkDCAStatusSel_PclkDCADebugLaneSel = this.PclkDCAStatusSel.PclkDCADebugLaneSel;
		this.PclkDCADebugLaneSel = this.PclkDCAStatusSel.PclkDCADebugLaneSel;
		this.PclkDCAStatusSel_PclkDCADebugInfoSel = this.PclkDCAStatusSel.PclkDCADebugInfoSel;
		this.PclkDCADebugInfoSel = this.PclkDCAStatusSel.PclkDCADebugInfoSel;
      this.PclkDCAStatusInfo = ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAStatusInfo::type_id::create("PclkDCAStatusInfo",,get_full_name());
      if(this.PclkDCAStatusInfo.has_coverage(UVM_CVR_ALL))
      	this.PclkDCAStatusInfo.cg_bits.option.name = {get_name(), ".", "PclkDCAStatusInfo_bits"};
      this.PclkDCAStatusInfo.configure(this, null, "");
      this.PclkDCAStatusInfo.build();
      this.default_map.add_reg(this.PclkDCAStatusInfo, `UVM_REG_ADDR_WIDTH'h512, "RO", 0);
		this.PclkDCAStatusInfo_PclkDCAStatusInfo = this.PclkDCAStatusInfo.PclkDCAStatusInfo;
      this.PclkDCACoarseBoundAC = ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACoarseBoundAC::type_id::create("PclkDCACoarseBoundAC",,get_full_name());
      if(this.PclkDCACoarseBoundAC.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACoarseBoundAC.cg_bits.option.name = {get_name(), ".", "PclkDCACoarseBoundAC_bits"};
      this.PclkDCACoarseBoundAC.configure(this, null, "");
      this.PclkDCACoarseBoundAC.build();
      this.default_map.add_reg(this.PclkDCACoarseBoundAC, `UVM_REG_ADDR_WIDTH'h51C, "RW", 0);
		this.PclkDCACoarseBoundAC_PclkDCAMaxCoarseAC = this.PclkDCACoarseBoundAC.PclkDCAMaxCoarseAC;
		this.PclkDCAMaxCoarseAC = this.PclkDCACoarseBoundAC.PclkDCAMaxCoarseAC;
		this.PclkDCACoarseBoundAC_PclkDCAMinCoarseAC = this.PclkDCACoarseBoundAC.PclkDCAMinCoarseAC;
		this.PclkDCAMinCoarseAC = this.PclkDCACoarseBoundAC.PclkDCAMinCoarseAC;
      this.PclkDCAMiscCtrlAC = ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAMiscCtrlAC::type_id::create("PclkDCAMiscCtrlAC",,get_full_name());
      if(this.PclkDCAMiscCtrlAC.has_coverage(UVM_CVR_ALL))
      	this.PclkDCAMiscCtrlAC.cg_bits.option.name = {get_name(), ".", "PclkDCAMiscCtrlAC_bits"};
      this.PclkDCAMiscCtrlAC.configure(this, null, "");
      this.PclkDCAMiscCtrlAC.build();
      this.default_map.add_reg(this.PclkDCAMiscCtrlAC, `UVM_REG_ADDR_WIDTH'h51E, "RW", 0);
		this.PclkDCAMiscCtrlAC_PclkDCADitherModeAC = this.PclkDCAMiscCtrlAC.PclkDCADitherModeAC;
		this.PclkDCADitherModeAC = this.PclkDCAMiscCtrlAC.PclkDCADitherModeAC;
		this.PclkDCAMiscCtrlAC_PclkDCDForceCkEnAC = this.PclkDCAMiscCtrlAC.PclkDCDForceCkEnAC;
		this.PclkDCDForceCkEnAC = this.PclkDCAMiscCtrlAC.PclkDCDForceCkEnAC;
		this.PclkDCAMiscCtrlAC_PclkDCAReservedAC = this.PclkDCAMiscCtrlAC.PclkDCAReservedAC;
		this.PclkDCAReservedAC = this.PclkDCAMiscCtrlAC.PclkDCAReservedAC;
      this.PclkDCDOffsetAC0_p0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCDOffsetAC0_p0::type_id::create("PclkDCDOffsetAC0_p0",,get_full_name());
      if(this.PclkDCDOffsetAC0_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCDOffsetAC0_p0.cg_bits.option.name = {get_name(), ".", "PclkDCDOffsetAC0_p0_bits"};
      this.PclkDCDOffsetAC0_p0.configure(this, null, "");
      this.PclkDCDOffsetAC0_p0.build();
      this.default_map.add_reg(this.PclkDCDOffsetAC0_p0, `UVM_REG_ADDR_WIDTH'h560, "RW", 0);
		this.PclkDCDOffsetAC0_p0_PclkDCDOffsetAC0_p0 = this.PclkDCDOffsetAC0_p0.PclkDCDOffsetAC0_p0;
      this.PclkDCDOffsetAC1_p0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCDOffsetAC1_p0::type_id::create("PclkDCDOffsetAC1_p0",,get_full_name());
      if(this.PclkDCDOffsetAC1_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCDOffsetAC1_p0.cg_bits.option.name = {get_name(), ".", "PclkDCDOffsetAC1_p0_bits"};
      this.PclkDCDOffsetAC1_p0.configure(this, null, "");
      this.PclkDCDOffsetAC1_p0.build();
      this.default_map.add_reg(this.PclkDCDOffsetAC1_p0, `UVM_REG_ADDR_WIDTH'h561, "RW", 0);
		this.PclkDCDOffsetAC1_p0_PclkDCDOffsetAC1_p0 = this.PclkDCDOffsetAC1_p0.PclkDCDOffsetAC1_p0;
      this.PclkDCALcdlCalCtrl = ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCALcdlCalCtrl::type_id::create("PclkDCALcdlCalCtrl",,get_full_name());
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
      this.DlyTestCntRingOscSelACX = ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestCntRingOscSelACX::type_id::create("DlyTestCntRingOscSelACX",,get_full_name());
      if(this.DlyTestCntRingOscSelACX.has_coverage(UVM_CVR_ALL))
      	this.DlyTestCntRingOscSelACX.cg_bits.option.name = {get_name(), ".", "DlyTestCntRingOscSelACX_bits"};
      this.DlyTestCntRingOscSelACX.configure(this, null, "");
      this.DlyTestCntRingOscSelACX.build();
      this.default_map.add_reg(this.DlyTestCntRingOscSelACX, `UVM_REG_ADDR_WIDTH'h592, "RW", 0);
		this.DlyTestCntRingOscSelACX_DlyTestCntRingOscSelACX = this.DlyTestCntRingOscSelACX.DlyTestCntRingOscSelACX;
      this.DlyTestRingSelACX = ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestRingSelACX::type_id::create("DlyTestRingSelACX",,get_full_name());
      if(this.DlyTestRingSelACX.has_coverage(UVM_CVR_ALL))
      	this.DlyTestRingSelACX.cg_bits.option.name = {get_name(), ".", "DlyTestRingSelACX_bits"};
      this.DlyTestRingSelACX.configure(this, null, "");
      this.DlyTestRingSelACX.build();
      this.default_map.add_reg(this.DlyTestRingSelACX, `UVM_REG_ADDR_WIDTH'h5D2, "RW", 0);
		this.DlyTestRingSelACX_DlyTestRingSelACX = this.DlyTestRingSelACX.DlyTestRingSelACX;
      this.DlyTestCntDfiClkIVHM = ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestCntDfiClkIVHM::type_id::create("DlyTestCntDfiClkIVHM",,get_full_name());
      if(this.DlyTestCntDfiClkIVHM.has_coverage(UVM_CVR_ALL))
      	this.DlyTestCntDfiClkIVHM.cg_bits.option.name = {get_name(), ".", "DlyTestCntDfiClkIVHM_bits"};
      this.DlyTestCntDfiClkIVHM.configure(this, null, "");
      this.DlyTestCntDfiClkIVHM.build();
      this.default_map.add_reg(this.DlyTestCntDfiClkIVHM, `UVM_REG_ADDR_WIDTH'h5D3, "RW", 0);
		this.DlyTestCntDfiClkIVHM_DlyTestCntDfiClkIVHM = this.DlyTestCntDfiClkIVHM.DlyTestCntDfiClkIVHM;
      this.DlyTestCntDfiClkHM = ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestCntDfiClkHM::type_id::create("DlyTestCntDfiClkHM",,get_full_name());
      if(this.DlyTestCntDfiClkHM.has_coverage(UVM_CVR_ALL))
      	this.DlyTestCntDfiClkHM.cg_bits.option.name = {get_name(), ".", "DlyTestCntDfiClkHM_bits"};
      this.DlyTestCntDfiClkHM.configure(this, null, "");
      this.DlyTestCntDfiClkHM.build();
      this.default_map.add_reg(this.DlyTestCntDfiClkHM, `UVM_REG_ADDR_WIDTH'h5D4, "RO", 0);
		this.DlyTestCntDfiClkHM_DlyTestCntDfiClkHM = this.DlyTestCntDfiClkHM.DlyTestCntDfiClkHM;
      this.DlyTestCntRingOsc = ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestCntRingOsc::type_id::create("DlyTestCntRingOsc",,get_full_name());
      if(this.DlyTestCntRingOsc.has_coverage(UVM_CVR_ALL))
      	this.DlyTestCntRingOsc.cg_bits.option.name = {get_name(), ".", "DlyTestCntRingOsc_bits"};
      this.DlyTestCntRingOsc.configure(this, null, "");
      this.DlyTestCntRingOsc.build();
      this.default_map.add_reg(this.DlyTestCntRingOsc, `UVM_REG_ADDR_WIDTH'h5D5, "RO", 0);
		this.DlyTestCntRingOsc_DlyTestCntRingOsc = this.DlyTestCntRingOsc.DlyTestCntRingOsc;
      this.DlyTestSeqHMAC = ral_reg_DWC_DDRPHYA_HMAC1_p0_DlyTestSeqHMAC::type_id::create("DlyTestSeqHMAC",,get_full_name());
      if(this.DlyTestSeqHMAC.has_coverage(UVM_CVR_ALL))
      	this.DlyTestSeqHMAC.cg_bits.option.name = {get_name(), ".", "DlyTestSeqHMAC_bits"};
      this.DlyTestSeqHMAC.configure(this, null, "");
      this.DlyTestSeqHMAC.build();
      this.default_map.add_reg(this.DlyTestSeqHMAC, `UVM_REG_ADDR_WIDTH'h5DF, "RW", 0);
		this.DlyTestSeqHMAC_DlyTestSeqHMAC = this.DlyTestSeqHMAC.DlyTestSeqHMAC;
      this.PclkDCALcdlAddDlySampEn_p0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCALcdlAddDlySampEn_p0::type_id::create("PclkDCALcdlAddDlySampEn_p0",,get_full_name());
      if(this.PclkDCALcdlAddDlySampEn_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCALcdlAddDlySampEn_p0.cg_bits.option.name = {get_name(), ".", "PclkDCALcdlAddDlySampEn_p0_bits"};
      this.PclkDCALcdlAddDlySampEn_p0.configure(this, null, "");
      this.PclkDCALcdlAddDlySampEn_p0.build();
      this.default_map.add_reg(this.PclkDCALcdlAddDlySampEn_p0, `UVM_REG_ADDR_WIDTH'h5E3, "RW", 0);
		this.PclkDCALcdlAddDlySampEn_p0_PclkDCALcdlAddDlySampEn_p0 = this.PclkDCALcdlAddDlySampEn_p0.PclkDCALcdlAddDlySampEn_p0;
      this.PclkDCAClkGaterEnAC = ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCAClkGaterEnAC::type_id::create("PclkDCAClkGaterEnAC",,get_full_name());
      if(this.PclkDCAClkGaterEnAC.has_coverage(UVM_CVR_ALL))
      	this.PclkDCAClkGaterEnAC.cg_bits.option.name = {get_name(), ".", "PclkDCAClkGaterEnAC_bits"};
      this.PclkDCAClkGaterEnAC.configure(this, null, "");
      this.PclkDCAClkGaterEnAC.build();
      this.default_map.add_reg(this.PclkDCAClkGaterEnAC, `UVM_REG_ADDR_WIDTH'h61E, "RW", 0);
		this.PclkDCAClkGaterEnAC_PclkDCAClkGaterEnAC = this.PclkDCAClkGaterEnAC.PclkDCAClkGaterEnAC;
      this.PclkDCACodeAC0_p0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACodeAC0_p0::type_id::create("PclkDCACodeAC0_p0",,get_full_name());
      if(this.PclkDCACodeAC0_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACodeAC0_p0.cg_bits.option.name = {get_name(), ".", "PclkDCACodeAC0_p0_bits"};
      this.PclkDCACodeAC0_p0.configure(this, null, "");
      this.PclkDCACodeAC0_p0.build();
      this.default_map.add_reg(this.PclkDCACodeAC0_p0, `UVM_REG_ADDR_WIDTH'h660, "RW", 0);
		this.PclkDCACodeAC0_p0_PclkDCACoarseAC0 = this.PclkDCACodeAC0_p0.PclkDCACoarseAC0;
		this.PclkDCACoarseAC0 = this.PclkDCACodeAC0_p0.PclkDCACoarseAC0;
		this.PclkDCACodeAC0_p0_PclkDCAFineAC0 = this.PclkDCACodeAC0_p0.PclkDCAFineAC0;
		this.PclkDCAFineAC0 = this.PclkDCACodeAC0_p0.PclkDCAFineAC0;
      this.PclkDCACodeAC1_p0 = ral_reg_DWC_DDRPHYA_HMAC1_p0_PclkDCACodeAC1_p0::type_id::create("PclkDCACodeAC1_p0",,get_full_name());
      if(this.PclkDCACodeAC1_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACodeAC1_p0.cg_bits.option.name = {get_name(), ".", "PclkDCACodeAC1_p0_bits"};
      this.PclkDCACodeAC1_p0.configure(this, null, "");
      this.PclkDCACodeAC1_p0.build();
      this.default_map.add_reg(this.PclkDCACodeAC1_p0, `UVM_REG_ADDR_WIDTH'h661, "RW", 0);
		this.PclkDCACodeAC1_p0_PclkDCACoarseAC1 = this.PclkDCACodeAC1_p0.PclkDCACoarseAC1;
		this.PclkDCACoarseAC1 = this.PclkDCACodeAC1_p0.PclkDCACoarseAC1;
		this.PclkDCACodeAC1_p0_PclkDCAFineAC1 = this.PclkDCACodeAC1_p0.PclkDCAFineAC1;
		this.PclkDCAFineAC1 = this.PclkDCACodeAC1_p0.PclkDCAFineAC1;
   endfunction : build

	`uvm_object_utils(ral_block_DWC_DDRPHYA_HMAC1_p0)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_DDRPHYA_HMAC1_p0


endpackage
`endif
