`ifndef RAL_DWC_DDRPHYA_HMAC3_P1_PKG
`define RAL_DWC_DDRPHYA_HMAC3_P1_PKG

package ral_DWC_DDRPHYA_HMAC3_p1_pkg;
import uvm_pkg::*;

class ral_reg_DWC_DDRPHYA_HMAC3_p1_ACReservedP_p1 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC3_p1_ACReservedP_p1");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ReservedACPS = uvm_reg_field::type_id::create("ReservedACPS",,get_full_name());
      this.ReservedACPS.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC3_p1_ACReservedP_p1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC3_p1_ACReservedP_p1


class ral_reg_DWC_DDRPHYA_HMAC3_p1_HMTxLcdlSeed_p1 extends uvm_reg;
	rand uvm_reg_field HMTxLcdlSeed_p1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HMTxLcdlSeed_p1: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC3_p1_HMTxLcdlSeed_p1");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMTxLcdlSeed_p1 = uvm_reg_field::type_id::create("HMTxLcdlSeed_p1",,get_full_name());
      this.HMTxLcdlSeed_p1.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC3_p1_HMTxLcdlSeed_p1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC3_p1_HMTxLcdlSeed_p1


class ral_reg_DWC_DDRPHYA_HMAC3_p1_LcdlMonitorCtl_p1 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC3_p1_LcdlMonitorCtl_p1");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.StickyUnlckThrshld = uvm_reg_field::type_id::create("StickyUnlckThrshld",,get_full_name());
      this.StickyUnlckThrshld.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC3_p1_LcdlMonitorCtl_p1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC3_p1_LcdlMonitorCtl_p1


class ral_reg_DWC_DDRPHYA_HMAC3_p1_HMACLcdlCalDeltaMM_p1 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC3_p1_HMACLcdlCalDeltaMM_p1");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxLcdlCalDeltaMM = uvm_reg_field::type_id::create("TxLcdlCalDeltaMM",,get_full_name());
      this.TxLcdlCalDeltaMM.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC3_p1_HMACLcdlCalDeltaMM_p1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC3_p1_HMACLcdlCalDeltaMM_p1


class ral_reg_DWC_DDRPHYA_HMAC3_p1_TxACDcaModeLn0_p1 extends uvm_reg;
	rand uvm_reg_field TxACDcaModeLn0_p1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxACDcaModeLn0_p1: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMAC3_p1_TxACDcaModeLn0_p1");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxACDcaModeLn0_p1 = uvm_reg_field::type_id::create("TxACDcaModeLn0_p1",,get_full_name());
      this.TxACDcaModeLn0_p1.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC3_p1_TxACDcaModeLn0_p1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC3_p1_TxACDcaModeLn0_p1


class ral_reg_DWC_DDRPHYA_HMAC3_p1_TxACDcaModeLn1_p1 extends uvm_reg;
	rand uvm_reg_field TxACDcaModeLn1_p1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxACDcaModeLn1_p1: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMAC3_p1_TxACDcaModeLn1_p1");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxACDcaModeLn1_p1 = uvm_reg_field::type_id::create("TxACDcaModeLn1_p1",,get_full_name());
      this.TxACDcaModeLn1_p1.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC3_p1_TxACDcaModeLn1_p1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC3_p1_TxACDcaModeLn1_p1


class ral_reg_DWC_DDRPHYA_HMAC3_p1_TxSlewAC_p1 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC3_p1_TxSlewAC_p1");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC3_p1_TxSlewAC_p1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC3_p1_TxSlewAC_p1


class ral_reg_DWC_DDRPHYA_HMAC3_p1_TxImpedanceAC_p1 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC3_p1_TxImpedanceAC_p1");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC3_p1_TxImpedanceAC_p1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC3_p1_TxImpedanceAC_p1


class ral_reg_DWC_DDRPHYA_HMAC3_p1_OdtImpedanceAC_p1 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC3_p1_OdtImpedanceAC_p1");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC3_p1_OdtImpedanceAC_p1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC3_p1_OdtImpedanceAC_p1


class ral_reg_DWC_DDRPHYA_HMAC3_p1_HMReservedP1_p1 extends uvm_reg;
	rand uvm_reg_field HMReservedP1_p1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HMReservedP1_p1: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC3_p1_HMReservedP1_p1");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMReservedP1_p1 = uvm_reg_field::type_id::create("HMReservedP1_p1",,get_full_name());
      this.HMReservedP1_p1.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC3_p1_HMReservedP1_p1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC3_p1_HMReservedP1_p1


class ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCATxLcdlPhase_p1 extends uvm_reg;
	rand uvm_reg_field PclkDCATxLcdlPhase_p1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCATxLcdlPhase_p1: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC3_p1_PclkDCATxLcdlPhase_p1");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCATxLcdlPhase_p1 = uvm_reg_field::type_id::create("PclkDCATxLcdlPhase_p1",,get_full_name());
      this.PclkDCATxLcdlPhase_p1.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCATxLcdlPhase_p1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCATxLcdlPhase_p1


class ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCAStaticCtrl1AC_p1 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC3_p1_PclkDCAStaticCtrl1AC_p1");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCAStaticCtrl1AC_p1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCAStaticCtrl1AC_p1


class ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCASampDelayLCDLAC_p1 extends uvm_reg;
	rand uvm_reg_field PclkDCASampDelayLCDLAC_p1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCASampDelayLCDLAC_p1: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC3_p1_PclkDCASampDelayLCDLAC_p1");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCASampDelayLCDLAC_p1 = uvm_reg_field::type_id::create("PclkDCASampDelayLCDLAC_p1",,get_full_name());
      this.PclkDCASampDelayLCDLAC_p1.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCASampDelayLCDLAC_p1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCASampDelayLCDLAC_p1


class ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCDOffsetAC0_p1 extends uvm_reg;
	rand uvm_reg_field PclkDCDOffsetAC0_p1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCDOffsetAC0_p1: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC3_p1_PclkDCDOffsetAC0_p1");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCDOffsetAC0_p1 = uvm_reg_field::type_id::create("PclkDCDOffsetAC0_p1",,get_full_name());
      this.PclkDCDOffsetAC0_p1.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCDOffsetAC0_p1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCDOffsetAC0_p1


class ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCDOffsetAC1_p1 extends uvm_reg;
	rand uvm_reg_field PclkDCDOffsetAC1_p1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCDOffsetAC1_p1: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC3_p1_PclkDCDOffsetAC1_p1");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCDOffsetAC1_p1 = uvm_reg_field::type_id::create("PclkDCDOffsetAC1_p1",,get_full_name());
      this.PclkDCDOffsetAC1_p1.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCDOffsetAC1_p1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCDOffsetAC1_p1


class ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCALcdlAddDlySampEn_p1 extends uvm_reg;
	rand uvm_reg_field PclkDCALcdlAddDlySampEn_p1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCALcdlAddDlySampEn_p1: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMAC3_p1_PclkDCALcdlAddDlySampEn_p1");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCALcdlAddDlySampEn_p1 = uvm_reg_field::type_id::create("PclkDCALcdlAddDlySampEn_p1",,get_full_name());
      this.PclkDCALcdlAddDlySampEn_p1.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCALcdlAddDlySampEn_p1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCALcdlAddDlySampEn_p1


class ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCACodeAC0_p1 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC3_p1_PclkDCACodeAC0_p1");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCACodeAC0_p1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCACodeAC0_p1


class ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCACodeAC1_p1 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMAC3_p1_PclkDCACodeAC1_p1");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCACodeAC1_p1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCACodeAC1_p1


class ral_block_DWC_DDRPHYA_HMAC3_p1 extends uvm_reg_block;
	rand ral_reg_DWC_DDRPHYA_HMAC3_p1_ACReservedP_p1 ACReservedP_p1;
	rand ral_reg_DWC_DDRPHYA_HMAC3_p1_HMTxLcdlSeed_p1 HMTxLcdlSeed_p1;
	rand ral_reg_DWC_DDRPHYA_HMAC3_p1_LcdlMonitorCtl_p1 LcdlMonitorCtl_p1;
	rand ral_reg_DWC_DDRPHYA_HMAC3_p1_HMACLcdlCalDeltaMM_p1 HMACLcdlCalDeltaMM_p1;
	rand ral_reg_DWC_DDRPHYA_HMAC3_p1_TxACDcaModeLn0_p1 TxACDcaModeLn0_p1;
	rand ral_reg_DWC_DDRPHYA_HMAC3_p1_TxACDcaModeLn1_p1 TxACDcaModeLn1_p1;
	rand ral_reg_DWC_DDRPHYA_HMAC3_p1_TxSlewAC_p1 TxSlewAC_p1;
	rand ral_reg_DWC_DDRPHYA_HMAC3_p1_TxImpedanceAC_p1 TxImpedanceAC_p1;
	rand ral_reg_DWC_DDRPHYA_HMAC3_p1_OdtImpedanceAC_p1 OdtImpedanceAC_p1;
	rand ral_reg_DWC_DDRPHYA_HMAC3_p1_HMReservedP1_p1 HMReservedP1_p1;
	rand ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCATxLcdlPhase_p1 PclkDCATxLcdlPhase_p1;
	rand ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCAStaticCtrl1AC_p1 PclkDCAStaticCtrl1AC_p1;
	rand ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCASampDelayLCDLAC_p1 PclkDCASampDelayLCDLAC_p1;
	rand ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCDOffsetAC0_p1 PclkDCDOffsetAC0_p1;
	rand ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCDOffsetAC1_p1 PclkDCDOffsetAC1_p1;
	rand ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCALcdlAddDlySampEn_p1 PclkDCALcdlAddDlySampEn_p1;
	rand ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCACodeAC0_p1 PclkDCACodeAC0_p1;
	rand ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCACodeAC1_p1 PclkDCACodeAC1_p1;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field ACReservedP_p1_ReservedACPS;
	rand uvm_reg_field ReservedACPS;
	rand uvm_reg_field HMTxLcdlSeed_p1_HMTxLcdlSeed_p1;
	rand uvm_reg_field LcdlMonitorCtl_p1_StickyUnlckThrshld;
	rand uvm_reg_field StickyUnlckThrshld;
	rand uvm_reg_field HMACLcdlCalDeltaMM_p1_TxLcdlCalDeltaMM;
	rand uvm_reg_field TxLcdlCalDeltaMM;
	rand uvm_reg_field TxACDcaModeLn0_p1_TxACDcaModeLn0_p1;
	rand uvm_reg_field TxACDcaModeLn1_p1_TxACDcaModeLn1_p1;
	rand uvm_reg_field TxSlewAC_p1_TxSlewPUAC;
	rand uvm_reg_field TxSlewPUAC;
	rand uvm_reg_field TxSlewAC_p1_TxSlewPDAC;
	rand uvm_reg_field TxSlewPDAC;
	rand uvm_reg_field TxImpedanceAC_p1_TxStrenCodePUAC;
	rand uvm_reg_field TxStrenCodePUAC;
	rand uvm_reg_field TxImpedanceAC_p1_TxStrenCodePDAC;
	rand uvm_reg_field TxStrenCodePDAC;
	rand uvm_reg_field OdtImpedanceAC_p1_OdtStrenCodePUAC;
	rand uvm_reg_field OdtStrenCodePUAC;
	rand uvm_reg_field OdtImpedanceAC_p1_OdtStrenCodePDAC;
	rand uvm_reg_field OdtStrenCodePDAC;
	rand uvm_reg_field HMReservedP1_p1_HMReservedP1_p1;
	rand uvm_reg_field PclkDCATxLcdlPhase_p1_PclkDCATxLcdlPhase_p1;
	rand uvm_reg_field PclkDCAStaticCtrl1AC_p1_PclkDCAInvertSampAC;
	rand uvm_reg_field PclkDCAInvertSampAC;
	rand uvm_reg_field PclkDCAStaticCtrl1AC_p1_PclkDCALcdlEn4pAC;
	rand uvm_reg_field PclkDCALcdlEn4pAC;
	rand uvm_reg_field PclkDCAStaticCtrl1AC_p1_PclkDCDMissionModeDelayAC;
	rand uvm_reg_field PclkDCDMissionModeDelayAC;
	rand uvm_reg_field PclkDCASampDelayLCDLAC_p1_PclkDCASampDelayLCDLAC_p1;
	rand uvm_reg_field PclkDCDOffsetAC0_p1_PclkDCDOffsetAC0_p1;
	rand uvm_reg_field PclkDCDOffsetAC1_p1_PclkDCDOffsetAC1_p1;
	rand uvm_reg_field PclkDCALcdlAddDlySampEn_p1_PclkDCALcdlAddDlySampEn_p1;
	rand uvm_reg_field PclkDCACodeAC0_p1_PclkDCACoarseAC0;
	rand uvm_reg_field PclkDCACoarseAC0;
	rand uvm_reg_field PclkDCACodeAC0_p1_PclkDCAFineAC0;
	rand uvm_reg_field PclkDCAFineAC0;
	rand uvm_reg_field PclkDCACodeAC1_p1_PclkDCACoarseAC1;
	rand uvm_reg_field PclkDCACoarseAC1;
	rand uvm_reg_field PclkDCACodeAC1_p1_PclkDCAFineAC1;
	rand uvm_reg_field PclkDCAFineAC1;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	ACReservedP_p1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h47 };
		option.weight = 1;
	}

	HMTxLcdlSeed_p1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h63 };
		option.weight = 1;
	}

	LcdlMonitorCtl_p1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h66 };
		option.weight = 1;
	}

	HMACLcdlCalDeltaMM_p1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h67 };
		option.weight = 1;
	}

	TxACDcaModeLn0_p1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h68 };
		option.weight = 1;
	}

	TxACDcaModeLn1_p1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h69 };
		option.weight = 1;
	}

	TxSlewAC_p1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h6D };
		option.weight = 1;
	}

	TxImpedanceAC_p1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h70 };
		option.weight = 1;
	}

	OdtImpedanceAC_p1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h79 };
		option.weight = 1;
	}

	HMReservedP1_p1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFF };
		option.weight = 1;
	}

	PclkDCATxLcdlPhase_p1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h110 };
		option.weight = 1;
	}

	PclkDCAStaticCtrl1AC_p1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h503 };
		option.weight = 1;
	}

	PclkDCASampDelayLCDLAC_p1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h50A };
		option.weight = 1;
	}

	PclkDCDOffsetAC0_p1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h560 };
		option.weight = 1;
	}

	PclkDCDOffsetAC1_p1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h561 };
		option.weight = 1;
	}

	PclkDCALcdlAddDlySampEn_p1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5E3 };
		option.weight = 1;
	}

	PclkDCACodeAC0_p1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h660 };
		option.weight = 1;
	}

	PclkDCACodeAC1_p1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h661 };
		option.weight = 1;
	}
endgroup
	function new(string name = "DWC_DDRPHYA_HMAC3_p1");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.ACReservedP_p1 = ral_reg_DWC_DDRPHYA_HMAC3_p1_ACReservedP_p1::type_id::create("ACReservedP_p1",,get_full_name());
      if(this.ACReservedP_p1.has_coverage(UVM_CVR_ALL))
      	this.ACReservedP_p1.cg_bits.option.name = {get_name(), ".", "ACReservedP_p1_bits"};
      this.ACReservedP_p1.configure(this, null, "");
      this.ACReservedP_p1.build();
      this.default_map.add_reg(this.ACReservedP_p1, `UVM_REG_ADDR_WIDTH'h47, "RW", 0);
		this.ACReservedP_p1_ReservedACPS = this.ACReservedP_p1.ReservedACPS;
		this.ReservedACPS = this.ACReservedP_p1.ReservedACPS;
      this.HMTxLcdlSeed_p1 = ral_reg_DWC_DDRPHYA_HMAC3_p1_HMTxLcdlSeed_p1::type_id::create("HMTxLcdlSeed_p1",,get_full_name());
      if(this.HMTxLcdlSeed_p1.has_coverage(UVM_CVR_ALL))
      	this.HMTxLcdlSeed_p1.cg_bits.option.name = {get_name(), ".", "HMTxLcdlSeed_p1_bits"};
      this.HMTxLcdlSeed_p1.configure(this, null, "");
      this.HMTxLcdlSeed_p1.build();
      this.default_map.add_reg(this.HMTxLcdlSeed_p1, `UVM_REG_ADDR_WIDTH'h63, "RW", 0);
		this.HMTxLcdlSeed_p1_HMTxLcdlSeed_p1 = this.HMTxLcdlSeed_p1.HMTxLcdlSeed_p1;
      this.LcdlMonitorCtl_p1 = ral_reg_DWC_DDRPHYA_HMAC3_p1_LcdlMonitorCtl_p1::type_id::create("LcdlMonitorCtl_p1",,get_full_name());
      if(this.LcdlMonitorCtl_p1.has_coverage(UVM_CVR_ALL))
      	this.LcdlMonitorCtl_p1.cg_bits.option.name = {get_name(), ".", "LcdlMonitorCtl_p1_bits"};
      this.LcdlMonitorCtl_p1.configure(this, null, "");
      this.LcdlMonitorCtl_p1.build();
      this.default_map.add_reg(this.LcdlMonitorCtl_p1, `UVM_REG_ADDR_WIDTH'h66, "RW", 0);
		this.LcdlMonitorCtl_p1_StickyUnlckThrshld = this.LcdlMonitorCtl_p1.StickyUnlckThrshld;
		this.StickyUnlckThrshld = this.LcdlMonitorCtl_p1.StickyUnlckThrshld;
      this.HMACLcdlCalDeltaMM_p1 = ral_reg_DWC_DDRPHYA_HMAC3_p1_HMACLcdlCalDeltaMM_p1::type_id::create("HMACLcdlCalDeltaMM_p1",,get_full_name());
      if(this.HMACLcdlCalDeltaMM_p1.has_coverage(UVM_CVR_ALL))
      	this.HMACLcdlCalDeltaMM_p1.cg_bits.option.name = {get_name(), ".", "HMACLcdlCalDeltaMM_p1_bits"};
      this.HMACLcdlCalDeltaMM_p1.configure(this, null, "");
      this.HMACLcdlCalDeltaMM_p1.build();
      this.default_map.add_reg(this.HMACLcdlCalDeltaMM_p1, `UVM_REG_ADDR_WIDTH'h67, "RW", 0);
		this.HMACLcdlCalDeltaMM_p1_TxLcdlCalDeltaMM = this.HMACLcdlCalDeltaMM_p1.TxLcdlCalDeltaMM;
		this.TxLcdlCalDeltaMM = this.HMACLcdlCalDeltaMM_p1.TxLcdlCalDeltaMM;
      this.TxACDcaModeLn0_p1 = ral_reg_DWC_DDRPHYA_HMAC3_p1_TxACDcaModeLn0_p1::type_id::create("TxACDcaModeLn0_p1",,get_full_name());
      if(this.TxACDcaModeLn0_p1.has_coverage(UVM_CVR_ALL))
      	this.TxACDcaModeLn0_p1.cg_bits.option.name = {get_name(), ".", "TxACDcaModeLn0_p1_bits"};
      this.TxACDcaModeLn0_p1.configure(this, null, "");
      this.TxACDcaModeLn0_p1.build();
      this.default_map.add_reg(this.TxACDcaModeLn0_p1, `UVM_REG_ADDR_WIDTH'h68, "RW", 0);
		this.TxACDcaModeLn0_p1_TxACDcaModeLn0_p1 = this.TxACDcaModeLn0_p1.TxACDcaModeLn0_p1;
      this.TxACDcaModeLn1_p1 = ral_reg_DWC_DDRPHYA_HMAC3_p1_TxACDcaModeLn1_p1::type_id::create("TxACDcaModeLn1_p1",,get_full_name());
      if(this.TxACDcaModeLn1_p1.has_coverage(UVM_CVR_ALL))
      	this.TxACDcaModeLn1_p1.cg_bits.option.name = {get_name(), ".", "TxACDcaModeLn1_p1_bits"};
      this.TxACDcaModeLn1_p1.configure(this, null, "");
      this.TxACDcaModeLn1_p1.build();
      this.default_map.add_reg(this.TxACDcaModeLn1_p1, `UVM_REG_ADDR_WIDTH'h69, "RW", 0);
		this.TxACDcaModeLn1_p1_TxACDcaModeLn1_p1 = this.TxACDcaModeLn1_p1.TxACDcaModeLn1_p1;
      this.TxSlewAC_p1 = ral_reg_DWC_DDRPHYA_HMAC3_p1_TxSlewAC_p1::type_id::create("TxSlewAC_p1",,get_full_name());
      if(this.TxSlewAC_p1.has_coverage(UVM_CVR_ALL))
      	this.TxSlewAC_p1.cg_bits.option.name = {get_name(), ".", "TxSlewAC_p1_bits"};
      this.TxSlewAC_p1.configure(this, null, "");
      this.TxSlewAC_p1.build();
      this.default_map.add_reg(this.TxSlewAC_p1, `UVM_REG_ADDR_WIDTH'h6D, "RW", 0);
		this.TxSlewAC_p1_TxSlewPUAC = this.TxSlewAC_p1.TxSlewPUAC;
		this.TxSlewPUAC = this.TxSlewAC_p1.TxSlewPUAC;
		this.TxSlewAC_p1_TxSlewPDAC = this.TxSlewAC_p1.TxSlewPDAC;
		this.TxSlewPDAC = this.TxSlewAC_p1.TxSlewPDAC;
      this.TxImpedanceAC_p1 = ral_reg_DWC_DDRPHYA_HMAC3_p1_TxImpedanceAC_p1::type_id::create("TxImpedanceAC_p1",,get_full_name());
      if(this.TxImpedanceAC_p1.has_coverage(UVM_CVR_ALL))
      	this.TxImpedanceAC_p1.cg_bits.option.name = {get_name(), ".", "TxImpedanceAC_p1_bits"};
      this.TxImpedanceAC_p1.configure(this, null, "");
      this.TxImpedanceAC_p1.build();
      this.default_map.add_reg(this.TxImpedanceAC_p1, `UVM_REG_ADDR_WIDTH'h70, "RW", 0);
		this.TxImpedanceAC_p1_TxStrenCodePUAC = this.TxImpedanceAC_p1.TxStrenCodePUAC;
		this.TxStrenCodePUAC = this.TxImpedanceAC_p1.TxStrenCodePUAC;
		this.TxImpedanceAC_p1_TxStrenCodePDAC = this.TxImpedanceAC_p1.TxStrenCodePDAC;
		this.TxStrenCodePDAC = this.TxImpedanceAC_p1.TxStrenCodePDAC;
      this.OdtImpedanceAC_p1 = ral_reg_DWC_DDRPHYA_HMAC3_p1_OdtImpedanceAC_p1::type_id::create("OdtImpedanceAC_p1",,get_full_name());
      if(this.OdtImpedanceAC_p1.has_coverage(UVM_CVR_ALL))
      	this.OdtImpedanceAC_p1.cg_bits.option.name = {get_name(), ".", "OdtImpedanceAC_p1_bits"};
      this.OdtImpedanceAC_p1.configure(this, null, "");
      this.OdtImpedanceAC_p1.build();
      this.default_map.add_reg(this.OdtImpedanceAC_p1, `UVM_REG_ADDR_WIDTH'h79, "RW", 0);
		this.OdtImpedanceAC_p1_OdtStrenCodePUAC = this.OdtImpedanceAC_p1.OdtStrenCodePUAC;
		this.OdtStrenCodePUAC = this.OdtImpedanceAC_p1.OdtStrenCodePUAC;
		this.OdtImpedanceAC_p1_OdtStrenCodePDAC = this.OdtImpedanceAC_p1.OdtStrenCodePDAC;
		this.OdtStrenCodePDAC = this.OdtImpedanceAC_p1.OdtStrenCodePDAC;
      this.HMReservedP1_p1 = ral_reg_DWC_DDRPHYA_HMAC3_p1_HMReservedP1_p1::type_id::create("HMReservedP1_p1",,get_full_name());
      if(this.HMReservedP1_p1.has_coverage(UVM_CVR_ALL))
      	this.HMReservedP1_p1.cg_bits.option.name = {get_name(), ".", "HMReservedP1_p1_bits"};
      this.HMReservedP1_p1.configure(this, null, "");
      this.HMReservedP1_p1.build();
      this.default_map.add_reg(this.HMReservedP1_p1, `UVM_REG_ADDR_WIDTH'hFF, "RW", 0);
		this.HMReservedP1_p1_HMReservedP1_p1 = this.HMReservedP1_p1.HMReservedP1_p1;
      this.PclkDCATxLcdlPhase_p1 = ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCATxLcdlPhase_p1::type_id::create("PclkDCATxLcdlPhase_p1",,get_full_name());
      if(this.PclkDCATxLcdlPhase_p1.has_coverage(UVM_CVR_ALL))
      	this.PclkDCATxLcdlPhase_p1.cg_bits.option.name = {get_name(), ".", "PclkDCATxLcdlPhase_p1_bits"};
      this.PclkDCATxLcdlPhase_p1.configure(this, null, "");
      this.PclkDCATxLcdlPhase_p1.build();
      this.default_map.add_reg(this.PclkDCATxLcdlPhase_p1, `UVM_REG_ADDR_WIDTH'h110, "RW", 0);
		this.PclkDCATxLcdlPhase_p1_PclkDCATxLcdlPhase_p1 = this.PclkDCATxLcdlPhase_p1.PclkDCATxLcdlPhase_p1;
      this.PclkDCAStaticCtrl1AC_p1 = ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCAStaticCtrl1AC_p1::type_id::create("PclkDCAStaticCtrl1AC_p1",,get_full_name());
      if(this.PclkDCAStaticCtrl1AC_p1.has_coverage(UVM_CVR_ALL))
      	this.PclkDCAStaticCtrl1AC_p1.cg_bits.option.name = {get_name(), ".", "PclkDCAStaticCtrl1AC_p1_bits"};
      this.PclkDCAStaticCtrl1AC_p1.configure(this, null, "");
      this.PclkDCAStaticCtrl1AC_p1.build();
      this.default_map.add_reg(this.PclkDCAStaticCtrl1AC_p1, `UVM_REG_ADDR_WIDTH'h503, "RW", 0);
		this.PclkDCAStaticCtrl1AC_p1_PclkDCAInvertSampAC = this.PclkDCAStaticCtrl1AC_p1.PclkDCAInvertSampAC;
		this.PclkDCAInvertSampAC = this.PclkDCAStaticCtrl1AC_p1.PclkDCAInvertSampAC;
		this.PclkDCAStaticCtrl1AC_p1_PclkDCALcdlEn4pAC = this.PclkDCAStaticCtrl1AC_p1.PclkDCALcdlEn4pAC;
		this.PclkDCALcdlEn4pAC = this.PclkDCAStaticCtrl1AC_p1.PclkDCALcdlEn4pAC;
		this.PclkDCAStaticCtrl1AC_p1_PclkDCDMissionModeDelayAC = this.PclkDCAStaticCtrl1AC_p1.PclkDCDMissionModeDelayAC;
		this.PclkDCDMissionModeDelayAC = this.PclkDCAStaticCtrl1AC_p1.PclkDCDMissionModeDelayAC;
      this.PclkDCASampDelayLCDLAC_p1 = ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCASampDelayLCDLAC_p1::type_id::create("PclkDCASampDelayLCDLAC_p1",,get_full_name());
      if(this.PclkDCASampDelayLCDLAC_p1.has_coverage(UVM_CVR_ALL))
      	this.PclkDCASampDelayLCDLAC_p1.cg_bits.option.name = {get_name(), ".", "PclkDCASampDelayLCDLAC_p1_bits"};
      this.PclkDCASampDelayLCDLAC_p1.configure(this, null, "");
      this.PclkDCASampDelayLCDLAC_p1.build();
      this.default_map.add_reg(this.PclkDCASampDelayLCDLAC_p1, `UVM_REG_ADDR_WIDTH'h50A, "RW", 0);
		this.PclkDCASampDelayLCDLAC_p1_PclkDCASampDelayLCDLAC_p1 = this.PclkDCASampDelayLCDLAC_p1.PclkDCASampDelayLCDLAC_p1;
      this.PclkDCDOffsetAC0_p1 = ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCDOffsetAC0_p1::type_id::create("PclkDCDOffsetAC0_p1",,get_full_name());
      if(this.PclkDCDOffsetAC0_p1.has_coverage(UVM_CVR_ALL))
      	this.PclkDCDOffsetAC0_p1.cg_bits.option.name = {get_name(), ".", "PclkDCDOffsetAC0_p1_bits"};
      this.PclkDCDOffsetAC0_p1.configure(this, null, "");
      this.PclkDCDOffsetAC0_p1.build();
      this.default_map.add_reg(this.PclkDCDOffsetAC0_p1, `UVM_REG_ADDR_WIDTH'h560, "RW", 0);
		this.PclkDCDOffsetAC0_p1_PclkDCDOffsetAC0_p1 = this.PclkDCDOffsetAC0_p1.PclkDCDOffsetAC0_p1;
      this.PclkDCDOffsetAC1_p1 = ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCDOffsetAC1_p1::type_id::create("PclkDCDOffsetAC1_p1",,get_full_name());
      if(this.PclkDCDOffsetAC1_p1.has_coverage(UVM_CVR_ALL))
      	this.PclkDCDOffsetAC1_p1.cg_bits.option.name = {get_name(), ".", "PclkDCDOffsetAC1_p1_bits"};
      this.PclkDCDOffsetAC1_p1.configure(this, null, "");
      this.PclkDCDOffsetAC1_p1.build();
      this.default_map.add_reg(this.PclkDCDOffsetAC1_p1, `UVM_REG_ADDR_WIDTH'h561, "RW", 0);
		this.PclkDCDOffsetAC1_p1_PclkDCDOffsetAC1_p1 = this.PclkDCDOffsetAC1_p1.PclkDCDOffsetAC1_p1;
      this.PclkDCALcdlAddDlySampEn_p1 = ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCALcdlAddDlySampEn_p1::type_id::create("PclkDCALcdlAddDlySampEn_p1",,get_full_name());
      if(this.PclkDCALcdlAddDlySampEn_p1.has_coverage(UVM_CVR_ALL))
      	this.PclkDCALcdlAddDlySampEn_p1.cg_bits.option.name = {get_name(), ".", "PclkDCALcdlAddDlySampEn_p1_bits"};
      this.PclkDCALcdlAddDlySampEn_p1.configure(this, null, "");
      this.PclkDCALcdlAddDlySampEn_p1.build();
      this.default_map.add_reg(this.PclkDCALcdlAddDlySampEn_p1, `UVM_REG_ADDR_WIDTH'h5E3, "RW", 0);
		this.PclkDCALcdlAddDlySampEn_p1_PclkDCALcdlAddDlySampEn_p1 = this.PclkDCALcdlAddDlySampEn_p1.PclkDCALcdlAddDlySampEn_p1;
      this.PclkDCACodeAC0_p1 = ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCACodeAC0_p1::type_id::create("PclkDCACodeAC0_p1",,get_full_name());
      if(this.PclkDCACodeAC0_p1.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACodeAC0_p1.cg_bits.option.name = {get_name(), ".", "PclkDCACodeAC0_p1_bits"};
      this.PclkDCACodeAC0_p1.configure(this, null, "");
      this.PclkDCACodeAC0_p1.build();
      this.default_map.add_reg(this.PclkDCACodeAC0_p1, `UVM_REG_ADDR_WIDTH'h660, "RW", 0);
		this.PclkDCACodeAC0_p1_PclkDCACoarseAC0 = this.PclkDCACodeAC0_p1.PclkDCACoarseAC0;
		this.PclkDCACoarseAC0 = this.PclkDCACodeAC0_p1.PclkDCACoarseAC0;
		this.PclkDCACodeAC0_p1_PclkDCAFineAC0 = this.PclkDCACodeAC0_p1.PclkDCAFineAC0;
		this.PclkDCAFineAC0 = this.PclkDCACodeAC0_p1.PclkDCAFineAC0;
      this.PclkDCACodeAC1_p1 = ral_reg_DWC_DDRPHYA_HMAC3_p1_PclkDCACodeAC1_p1::type_id::create("PclkDCACodeAC1_p1",,get_full_name());
      if(this.PclkDCACodeAC1_p1.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACodeAC1_p1.cg_bits.option.name = {get_name(), ".", "PclkDCACodeAC1_p1_bits"};
      this.PclkDCACodeAC1_p1.configure(this, null, "");
      this.PclkDCACodeAC1_p1.build();
      this.default_map.add_reg(this.PclkDCACodeAC1_p1, `UVM_REG_ADDR_WIDTH'h661, "RW", 0);
		this.PclkDCACodeAC1_p1_PclkDCACoarseAC1 = this.PclkDCACodeAC1_p1.PclkDCACoarseAC1;
		this.PclkDCACoarseAC1 = this.PclkDCACodeAC1_p1.PclkDCACoarseAC1;
		this.PclkDCACodeAC1_p1_PclkDCAFineAC1 = this.PclkDCACodeAC1_p1.PclkDCAFineAC1;
		this.PclkDCAFineAC1 = this.PclkDCACodeAC1_p1.PclkDCAFineAC1;
   endfunction : build

	`uvm_object_utils(ral_block_DWC_DDRPHYA_HMAC3_p1)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_DDRPHYA_HMAC3_p1


endpackage
`endif
