`ifndef RAL_DWC_DDRPHYA_APBONLY0_PKG
`define RAL_DWC_DDRPHYA_APBONLY0_PKG

package ral_DWC_DDRPHYA_APBONLY0_pkg;
import uvm_pkg::*;

class ral_reg_DWC_DDRPHYA_APBONLY0_MicroContMuxSel extends uvm_reg;
	rand uvm_reg_field MicroContMuxSel;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   MicroContMuxSel: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_MicroContMuxSel");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MicroContMuxSel = uvm_reg_field::type_id::create("MicroContMuxSel",,get_full_name());
      this.MicroContMuxSel.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_MicroContMuxSel)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_MicroContMuxSel


class ral_reg_DWC_DDRPHYA_APBONLY0_ContextToMicro extends uvm_reg;
	rand uvm_reg_field ContextToMicro;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ContextToMicro: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_ContextToMicro");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ContextToMicro = uvm_reg_field::type_id::create("ContextToMicro",,get_full_name());
      this.ContextToMicro.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_ContextToMicro)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_ContextToMicro


class ral_reg_DWC_DDRPHYA_APBONLY0_ExternalAHBReset extends uvm_reg;
	rand uvm_reg_field ExternalAHBReset;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ExternalAHBReset: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_ExternalAHBReset");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ExternalAHBReset = uvm_reg_field::type_id::create("ExternalAHBReset",,get_full_name());
      this.ExternalAHBReset.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_ExternalAHBReset)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_ExternalAHBReset


class ral_reg_DWC_DDRPHYA_APBONLY0_TDRDisable extends uvm_reg;
	rand uvm_reg_field TDRDisable;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TDRDisable: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_TDRDisable");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TDRDisable = uvm_reg_field::type_id::create("TDRDisable",,get_full_name());
      this.TDRDisable.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_TDRDisable)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_TDRDisable


class ral_reg_DWC_DDRPHYA_APBONLY0_UctShadowRegs extends uvm_reg;
	uvm_reg_field UctWriteProtShadow;
	uvm_reg_field UctDatWriteProtShadow;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   UctWriteProtShadow: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   UctDatWriteProtShadow: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_UctShadowRegs");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.UctWriteProtShadow = uvm_reg_field::type_id::create("UctWriteProtShadow",,get_full_name());
      this.UctWriteProtShadow.configure(this, 1, 0, "RO", 1, 1'h0, 1, 0, 0);
      this.UctDatWriteProtShadow = uvm_reg_field::type_id::create("UctDatWriteProtShadow",,get_full_name());
      this.UctDatWriteProtShadow.configure(this, 1, 1, "RO", 1, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_UctShadowRegs)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_UctShadowRegs


class ral_reg_DWC_DDRPHYA_APBONLY0_BlockDfiShadowRegs extends uvm_reg;
	uvm_reg_field BlockDfiInterfaceEnShadow;
	uvm_reg_field PmuBusyShadow;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   BlockDfiInterfaceEnShadow: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   PmuBusyShadow: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_BlockDfiShadowRegs");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.BlockDfiInterfaceEnShadow = uvm_reg_field::type_id::create("BlockDfiInterfaceEnShadow",,get_full_name());
      this.BlockDfiInterfaceEnShadow.configure(this, 1, 0, "RO", 1, 1'h0, 1, 0, 0);
      this.PmuBusyShadow = uvm_reg_field::type_id::create("PmuBusyShadow",,get_full_name());
      this.PmuBusyShadow.configure(this, 1, 1, "RO", 1, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_BlockDfiShadowRegs)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_BlockDfiShadowRegs


class ral_reg_DWC_DDRPHYA_APBONLY0_CCMWriteBypassEnable extends uvm_reg;
	rand uvm_reg_field CCMWriteBypassEnable;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CCMWriteBypassEnable: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_APBONLY0_CCMWriteBypassEnable");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CCMWriteBypassEnable = uvm_reg_field::type_id::create("CCMWriteBypassEnable",,get_full_name());
      this.CCMWriteBypassEnable.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_CCMWriteBypassEnable)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_CCMWriteBypassEnable


class ral_reg_DWC_DDRPHYA_APBONLY0_DctWriteOnly extends uvm_reg;
	rand uvm_reg_field DctWriteOnly;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DctWriteOnly: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_APBONLY0_DctWriteOnly");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DctWriteOnly = uvm_reg_field::type_id::create("DctWriteOnly",,get_full_name());
      this.DctWriteOnly.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_DctWriteOnly)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_DctWriteOnly


class ral_reg_DWC_DDRPHYA_APBONLY0_DctWriteProt extends uvm_reg;
	rand uvm_reg_field DctWriteProt;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DctWriteProt: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_DctWriteProt");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DctWriteProt = uvm_reg_field::type_id::create("DctWriteProt",,get_full_name());
      this.DctWriteProt.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_DctWriteProt)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_DctWriteProt


class ral_reg_DWC_DDRPHYA_APBONLY0_UctWriteOnlyShadow extends uvm_reg;
	uvm_reg_field UctWriteOnlyShadow;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   UctWriteOnlyShadow: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_APBONLY0_UctWriteOnlyShadow");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.UctWriteOnlyShadow = uvm_reg_field::type_id::create("UctWriteOnlyShadow",,get_full_name());
      this.UctWriteOnlyShadow.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_UctWriteOnlyShadow)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_UctWriteOnlyShadow


class ral_reg_DWC_DDRPHYA_APBONLY0_UctDatWriteOnlyShadow extends uvm_reg;
	uvm_reg_field UctDatWriteOnlyShadow;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   UctDatWriteOnlyShadow: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_APBONLY0_UctDatWriteOnlyShadow");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.UctDatWriteOnlyShadow = uvm_reg_field::type_id::create("UctDatWriteOnlyShadow",,get_full_name());
      this.UctDatWriteOnlyShadow.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_UctDatWriteOnlyShadow)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_UctDatWriteOnlyShadow


class ral_reg_DWC_DDRPHYA_APBONLY0_NeverGateCsrClock extends uvm_reg;
	rand uvm_reg_field NeverGateCsrClock;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   NeverGateCsrClock: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_NeverGateCsrClock");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.NeverGateCsrClock = uvm_reg_field::type_id::create("NeverGateCsrClock",,get_full_name());
      this.NeverGateCsrClock.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_NeverGateCsrClock)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_NeverGateCsrClock


class ral_reg_DWC_DDRPHYA_APBONLY0_NeverGateAcCsrClock extends uvm_reg;
	rand uvm_reg_field NeverGateAcCsrClock;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   NeverGateAcCsrClock: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_NeverGateAcCsrClock");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.NeverGateAcCsrClock = uvm_reg_field::type_id::create("NeverGateAcCsrClock",,get_full_name());
      this.NeverGateAcCsrClock.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_NeverGateAcCsrClock)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_NeverGateAcCsrClock


class ral_reg_DWC_DDRPHYA_APBONLY0_DfiCfgRdDataValidTicks extends uvm_reg;
	rand uvm_reg_field DfiCfgRdDataValidTicksARC;
	rand uvm_reg_field DfiCfgRdDataValidTicksReg;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiCfgRdDataValidTicksARC: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
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
	   DfiCfgRdDataValidTicksReg: coverpoint {m_data[11:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_APBONLY0_DfiCfgRdDataValidTicks");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiCfgRdDataValidTicksARC = uvm_reg_field::type_id::create("DfiCfgRdDataValidTicksARC",,get_full_name());
      this.DfiCfgRdDataValidTicksARC.configure(this, 6, 0, "RW", 0, 6'h18, 1, 0, 0);
      this.DfiCfgRdDataValidTicksReg = uvm_reg_field::type_id::create("DfiCfgRdDataValidTicksReg",,get_full_name());
      this.DfiCfgRdDataValidTicksReg.configure(this, 6, 6, "RW", 0, 6'h10, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_DfiCfgRdDataValidTicks)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_DfiCfgRdDataValidTicks


class ral_reg_DWC_DDRPHYA_APBONLY0_DisableHMRdSpeedUp extends uvm_reg;
	rand uvm_reg_field DisableHMRdSpeedUp;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DisableHMRdSpeedUp: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_DisableHMRdSpeedUp");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DisableHMRdSpeedUp = uvm_reg_field::type_id::create("DisableHMRdSpeedUp",,get_full_name());
      this.DisableHMRdSpeedUp.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_DisableHMRdSpeedUp)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_DisableHMRdSpeedUp


class ral_reg_DWC_DDRPHYA_APBONLY0_OverrideHMRdSpeedUp extends uvm_reg;
	rand uvm_reg_field OverrideHMRdSpeedUp;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   OverrideHMRdSpeedUp: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_APBONLY0_OverrideHMRdSpeedUp");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.OverrideHMRdSpeedUp = uvm_reg_field::type_id::create("OverrideHMRdSpeedUp",,get_full_name());
      this.OverrideHMRdSpeedUp.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_OverrideHMRdSpeedUp)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_OverrideHMRdSpeedUp


class ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugControl extends uvm_reg;
	rand uvm_reg_field Dfi0DebugControl;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   Dfi0DebugControl: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_APBONLY0_Dfi0DebugControl");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.Dfi0DebugControl = uvm_reg_field::type_id::create("Dfi0DebugControl",,get_full_name());
      this.Dfi0DebugControl.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugControl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugControl


class ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugCapture0 extends uvm_reg;
	uvm_reg_field Dfi0DebugCapture0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   Dfi0DebugCapture0: coverpoint {m_data[12:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {14'b????????????00};
	      wildcard bins bit_0_wr_as_1 = {14'b????????????10};
	      wildcard bins bit_0_rd = {14'b?????????????1};
	      wildcard bins bit_1_wr_as_0 = {14'b???????????0?0};
	      wildcard bins bit_1_wr_as_1 = {14'b???????????1?0};
	      wildcard bins bit_1_rd = {14'b?????????????1};
	      wildcard bins bit_2_wr_as_0 = {14'b??????????0??0};
	      wildcard bins bit_2_wr_as_1 = {14'b??????????1??0};
	      wildcard bins bit_2_rd = {14'b?????????????1};
	      wildcard bins bit_3_wr_as_0 = {14'b?????????0???0};
	      wildcard bins bit_3_wr_as_1 = {14'b?????????1???0};
	      wildcard bins bit_3_rd = {14'b?????????????1};
	      wildcard bins bit_4_wr_as_0 = {14'b????????0????0};
	      wildcard bins bit_4_wr_as_1 = {14'b????????1????0};
	      wildcard bins bit_4_rd = {14'b?????????????1};
	      wildcard bins bit_5_wr_as_0 = {14'b???????0?????0};
	      wildcard bins bit_5_wr_as_1 = {14'b???????1?????0};
	      wildcard bins bit_5_rd = {14'b?????????????1};
	      wildcard bins bit_6_wr_as_0 = {14'b??????0??????0};
	      wildcard bins bit_6_wr_as_1 = {14'b??????1??????0};
	      wildcard bins bit_6_rd = {14'b?????????????1};
	      wildcard bins bit_7_wr_as_0 = {14'b?????0???????0};
	      wildcard bins bit_7_wr_as_1 = {14'b?????1???????0};
	      wildcard bins bit_7_rd = {14'b?????????????1};
	      wildcard bins bit_8_wr_as_0 = {14'b????0????????0};
	      wildcard bins bit_8_wr_as_1 = {14'b????1????????0};
	      wildcard bins bit_8_rd = {14'b?????????????1};
	      wildcard bins bit_9_wr_as_0 = {14'b???0?????????0};
	      wildcard bins bit_9_wr_as_1 = {14'b???1?????????0};
	      wildcard bins bit_9_rd = {14'b?????????????1};
	      wildcard bins bit_10_wr_as_0 = {14'b??0??????????0};
	      wildcard bins bit_10_wr_as_1 = {14'b??1??????????0};
	      wildcard bins bit_10_rd = {14'b?????????????1};
	      wildcard bins bit_11_wr_as_0 = {14'b?0???????????0};
	      wildcard bins bit_11_wr_as_1 = {14'b?1???????????0};
	      wildcard bins bit_11_rd = {14'b?????????????1};
	      wildcard bins bit_12_wr_as_0 = {14'b0????????????0};
	      wildcard bins bit_12_wr_as_1 = {14'b1????????????0};
	      wildcard bins bit_12_rd = {14'b?????????????1};
	      option.weight = 39;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_Dfi0DebugCapture0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.Dfi0DebugCapture0 = uvm_reg_field::type_id::create("Dfi0DebugCapture0",,get_full_name());
      this.Dfi0DebugCapture0.configure(this, 13, 0, "RO", 1, 13'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugCapture0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugCapture0


class ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugCapture1 extends uvm_reg;
	uvm_reg_field Dfi0DebugCapture1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   Dfi0DebugCapture1: coverpoint {m_data[9:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {11'b?????????00};
	      wildcard bins bit_0_wr_as_1 = {11'b?????????10};
	      wildcard bins bit_0_rd = {11'b??????????1};
	      wildcard bins bit_1_wr_as_0 = {11'b????????0?0};
	      wildcard bins bit_1_wr_as_1 = {11'b????????1?0};
	      wildcard bins bit_1_rd = {11'b??????????1};
	      wildcard bins bit_2_wr_as_0 = {11'b???????0??0};
	      wildcard bins bit_2_wr_as_1 = {11'b???????1??0};
	      wildcard bins bit_2_rd = {11'b??????????1};
	      wildcard bins bit_3_wr_as_0 = {11'b??????0???0};
	      wildcard bins bit_3_wr_as_1 = {11'b??????1???0};
	      wildcard bins bit_3_rd = {11'b??????????1};
	      wildcard bins bit_4_wr_as_0 = {11'b?????0????0};
	      wildcard bins bit_4_wr_as_1 = {11'b?????1????0};
	      wildcard bins bit_4_rd = {11'b??????????1};
	      wildcard bins bit_5_wr_as_0 = {11'b????0?????0};
	      wildcard bins bit_5_wr_as_1 = {11'b????1?????0};
	      wildcard bins bit_5_rd = {11'b??????????1};
	      wildcard bins bit_6_wr_as_0 = {11'b???0??????0};
	      wildcard bins bit_6_wr_as_1 = {11'b???1??????0};
	      wildcard bins bit_6_rd = {11'b??????????1};
	      wildcard bins bit_7_wr_as_0 = {11'b??0???????0};
	      wildcard bins bit_7_wr_as_1 = {11'b??1???????0};
	      wildcard bins bit_7_rd = {11'b??????????1};
	      wildcard bins bit_8_wr_as_0 = {11'b?0????????0};
	      wildcard bins bit_8_wr_as_1 = {11'b?1????????0};
	      wildcard bins bit_8_rd = {11'b??????????1};
	      wildcard bins bit_9_wr_as_0 = {11'b0?????????0};
	      wildcard bins bit_9_wr_as_1 = {11'b1?????????0};
	      wildcard bins bit_9_rd = {11'b??????????1};
	      option.weight = 30;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_Dfi0DebugCapture1");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.Dfi0DebugCapture1 = uvm_reg_field::type_id::create("Dfi0DebugCapture1",,get_full_name());
      this.Dfi0DebugCapture1.configure(this, 10, 0, "RO", 1, 10'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugCapture1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugCapture1


class ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugPerfCtrEn extends uvm_reg;
	rand uvm_reg_field Dfi0DebugPerfCtrEn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   Dfi0DebugPerfCtrEn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_Dfi0DebugPerfCtrEn");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.Dfi0DebugPerfCtrEn = uvm_reg_field::type_id::create("Dfi0DebugPerfCtrEn",,get_full_name());
      this.Dfi0DebugPerfCtrEn.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugPerfCtrEn)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugPerfCtrEn


class ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugPerfCtr extends uvm_reg;
	uvm_reg_field Dfi0DebugPerfCtr;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   Dfi0DebugPerfCtr: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_APBONLY0_Dfi0DebugPerfCtr");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.Dfi0DebugPerfCtr = uvm_reg_field::type_id::create("Dfi0DebugPerfCtr",,get_full_name());
      this.Dfi0DebugPerfCtr.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugPerfCtr)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugPerfCtr


class ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugControl extends uvm_reg;
	rand uvm_reg_field Dfi1DebugControl;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   Dfi1DebugControl: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_APBONLY0_Dfi1DebugControl");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.Dfi1DebugControl = uvm_reg_field::type_id::create("Dfi1DebugControl",,get_full_name());
      this.Dfi1DebugControl.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugControl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugControl


class ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugCapture0 extends uvm_reg;
	uvm_reg_field Dfi1DebugCapture0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   Dfi1DebugCapture0: coverpoint {m_data[12:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {14'b????????????00};
	      wildcard bins bit_0_wr_as_1 = {14'b????????????10};
	      wildcard bins bit_0_rd = {14'b?????????????1};
	      wildcard bins bit_1_wr_as_0 = {14'b???????????0?0};
	      wildcard bins bit_1_wr_as_1 = {14'b???????????1?0};
	      wildcard bins bit_1_rd = {14'b?????????????1};
	      wildcard bins bit_2_wr_as_0 = {14'b??????????0??0};
	      wildcard bins bit_2_wr_as_1 = {14'b??????????1??0};
	      wildcard bins bit_2_rd = {14'b?????????????1};
	      wildcard bins bit_3_wr_as_0 = {14'b?????????0???0};
	      wildcard bins bit_3_wr_as_1 = {14'b?????????1???0};
	      wildcard bins bit_3_rd = {14'b?????????????1};
	      wildcard bins bit_4_wr_as_0 = {14'b????????0????0};
	      wildcard bins bit_4_wr_as_1 = {14'b????????1????0};
	      wildcard bins bit_4_rd = {14'b?????????????1};
	      wildcard bins bit_5_wr_as_0 = {14'b???????0?????0};
	      wildcard bins bit_5_wr_as_1 = {14'b???????1?????0};
	      wildcard bins bit_5_rd = {14'b?????????????1};
	      wildcard bins bit_6_wr_as_0 = {14'b??????0??????0};
	      wildcard bins bit_6_wr_as_1 = {14'b??????1??????0};
	      wildcard bins bit_6_rd = {14'b?????????????1};
	      wildcard bins bit_7_wr_as_0 = {14'b?????0???????0};
	      wildcard bins bit_7_wr_as_1 = {14'b?????1???????0};
	      wildcard bins bit_7_rd = {14'b?????????????1};
	      wildcard bins bit_8_wr_as_0 = {14'b????0????????0};
	      wildcard bins bit_8_wr_as_1 = {14'b????1????????0};
	      wildcard bins bit_8_rd = {14'b?????????????1};
	      wildcard bins bit_9_wr_as_0 = {14'b???0?????????0};
	      wildcard bins bit_9_wr_as_1 = {14'b???1?????????0};
	      wildcard bins bit_9_rd = {14'b?????????????1};
	      wildcard bins bit_10_wr_as_0 = {14'b??0??????????0};
	      wildcard bins bit_10_wr_as_1 = {14'b??1??????????0};
	      wildcard bins bit_10_rd = {14'b?????????????1};
	      wildcard bins bit_11_wr_as_0 = {14'b?0???????????0};
	      wildcard bins bit_11_wr_as_1 = {14'b?1???????????0};
	      wildcard bins bit_11_rd = {14'b?????????????1};
	      wildcard bins bit_12_wr_as_0 = {14'b0????????????0};
	      wildcard bins bit_12_wr_as_1 = {14'b1????????????0};
	      wildcard bins bit_12_rd = {14'b?????????????1};
	      option.weight = 39;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_Dfi1DebugCapture0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.Dfi1DebugCapture0 = uvm_reg_field::type_id::create("Dfi1DebugCapture0",,get_full_name());
      this.Dfi1DebugCapture0.configure(this, 13, 0, "RO", 1, 13'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugCapture0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugCapture0


class ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugCapture1 extends uvm_reg;
	uvm_reg_field Dfi1DebugCapture1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   Dfi1DebugCapture1: coverpoint {m_data[9:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {11'b?????????00};
	      wildcard bins bit_0_wr_as_1 = {11'b?????????10};
	      wildcard bins bit_0_rd = {11'b??????????1};
	      wildcard bins bit_1_wr_as_0 = {11'b????????0?0};
	      wildcard bins bit_1_wr_as_1 = {11'b????????1?0};
	      wildcard bins bit_1_rd = {11'b??????????1};
	      wildcard bins bit_2_wr_as_0 = {11'b???????0??0};
	      wildcard bins bit_2_wr_as_1 = {11'b???????1??0};
	      wildcard bins bit_2_rd = {11'b??????????1};
	      wildcard bins bit_3_wr_as_0 = {11'b??????0???0};
	      wildcard bins bit_3_wr_as_1 = {11'b??????1???0};
	      wildcard bins bit_3_rd = {11'b??????????1};
	      wildcard bins bit_4_wr_as_0 = {11'b?????0????0};
	      wildcard bins bit_4_wr_as_1 = {11'b?????1????0};
	      wildcard bins bit_4_rd = {11'b??????????1};
	      wildcard bins bit_5_wr_as_0 = {11'b????0?????0};
	      wildcard bins bit_5_wr_as_1 = {11'b????1?????0};
	      wildcard bins bit_5_rd = {11'b??????????1};
	      wildcard bins bit_6_wr_as_0 = {11'b???0??????0};
	      wildcard bins bit_6_wr_as_1 = {11'b???1??????0};
	      wildcard bins bit_6_rd = {11'b??????????1};
	      wildcard bins bit_7_wr_as_0 = {11'b??0???????0};
	      wildcard bins bit_7_wr_as_1 = {11'b??1???????0};
	      wildcard bins bit_7_rd = {11'b??????????1};
	      wildcard bins bit_8_wr_as_0 = {11'b?0????????0};
	      wildcard bins bit_8_wr_as_1 = {11'b?1????????0};
	      wildcard bins bit_8_rd = {11'b??????????1};
	      wildcard bins bit_9_wr_as_0 = {11'b0?????????0};
	      wildcard bins bit_9_wr_as_1 = {11'b1?????????0};
	      wildcard bins bit_9_rd = {11'b??????????1};
	      option.weight = 30;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_Dfi1DebugCapture1");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.Dfi1DebugCapture1 = uvm_reg_field::type_id::create("Dfi1DebugCapture1",,get_full_name());
      this.Dfi1DebugCapture1.configure(this, 10, 0, "RO", 1, 10'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugCapture1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugCapture1


class ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugPerfCtrEn extends uvm_reg;
	rand uvm_reg_field Dfi1DebugPerfCtrEn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   Dfi1DebugPerfCtrEn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_Dfi1DebugPerfCtrEn");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.Dfi1DebugPerfCtrEn = uvm_reg_field::type_id::create("Dfi1DebugPerfCtrEn",,get_full_name());
      this.Dfi1DebugPerfCtrEn.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugPerfCtrEn)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugPerfCtrEn


class ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugPerfCtr extends uvm_reg;
	uvm_reg_field Dfi1DebugPerfCtr;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   Dfi1DebugPerfCtr: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_APBONLY0_Dfi1DebugPerfCtr");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.Dfi1DebugPerfCtr = uvm_reg_field::type_id::create("Dfi1DebugPerfCtr",,get_full_name());
      this.Dfi1DebugPerfCtr.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugPerfCtr)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugPerfCtr


class ral_reg_DWC_DDRPHYA_APBONLY0_APBONLYParityInvert extends uvm_reg;
	rand uvm_reg_field APBONLYParityInvert;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   APBONLYParityInvert: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_APBONLY0_APBONLYParityInvert");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.APBONLYParityInvert = uvm_reg_field::type_id::create("APBONLYParityInvert",,get_full_name());
      this.APBONLYParityInvert.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_APBONLYParityInvert)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_APBONLYParityInvert


class ral_reg_DWC_DDRPHYA_APBONLY0_WaitCondAPB extends uvm_reg;
	rand uvm_reg_field WaitCondAPB;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   WaitCondAPB: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_WaitCondAPB");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.WaitCondAPB = uvm_reg_field::type_id::create("WaitCondAPB",,get_full_name());
      this.WaitCondAPB.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_WaitCondAPB)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_WaitCondAPB


class ral_reg_DWC_DDRPHYA_APBONLY0_PIERdDataValidTicks extends uvm_reg;
	rand uvm_reg_field PIERdDataValidTicksARC;
	rand uvm_reg_field PIERdDataValidTicksReg;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PIERdDataValidTicksARC: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
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
	   PIERdDataValidTicksReg: coverpoint {m_data[11:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_APBONLY0_PIERdDataValidTicks");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PIERdDataValidTicksARC = uvm_reg_field::type_id::create("PIERdDataValidTicksARC",,get_full_name());
      this.PIERdDataValidTicksARC.configure(this, 6, 0, "RW", 0, 6'hc, 1, 0, 0);
      this.PIERdDataValidTicksReg = uvm_reg_field::type_id::create("PIERdDataValidTicksReg",,get_full_name());
      this.PIERdDataValidTicksReg.configure(this, 6, 6, "RW", 0, 6'he, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_PIERdDataValidTicks)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_PIERdDataValidTicks


class ral_reg_DWC_DDRPHYA_APBONLY0_UCRdDataValidTicks extends uvm_reg;
	rand uvm_reg_field UCRdDataValidTicksARC;
	rand uvm_reg_field UCRdDataValidTicksReg;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   UCRdDataValidTicksARC: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
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
	   UCRdDataValidTicksReg: coverpoint {m_data[11:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_APBONLY0_UCRdDataValidTicks");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.UCRdDataValidTicksARC = uvm_reg_field::type_id::create("UCRdDataValidTicksARC",,get_full_name());
      this.UCRdDataValidTicksARC.configure(this, 6, 0, "RW", 0, 6'h0, 1, 0, 0);
      this.UCRdDataValidTicksReg = uvm_reg_field::type_id::create("UCRdDataValidTicksReg",,get_full_name());
      this.UCRdDataValidTicksReg.configure(this, 6, 6, "RW", 0, 6'hf, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_UCRdDataValidTicks)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_UCRdDataValidTicks


class ral_reg_DWC_DDRPHYA_APBONLY0_ScratchPadAPBONLY extends uvm_reg;
	rand uvm_reg_field ScratchPadAPBONLY;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ScratchPadAPBONLY: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_APBONLY0_ScratchPadAPBONLY");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ScratchPadAPBONLY = uvm_reg_field::type_id::create("ScratchPadAPBONLY",,get_full_name());
      this.ScratchPadAPBONLY.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_ScratchPadAPBONLY)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_ScratchPadAPBONLY


class ral_reg_DWC_DDRPHYA_APBONLY0_MicroReset extends uvm_reg;
	rand uvm_reg_field StallToMicro;
	rand uvm_reg_field TestWakeup;
	rand uvm_reg_field RSVDMicro;
	rand uvm_reg_field ResetToMicro;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   StallToMicro: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   TestWakeup: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   RSVDMicro: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ResetToMicro: coverpoint {m_data[3:3], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_MicroReset");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.StallToMicro = uvm_reg_field::type_id::create("StallToMicro",,get_full_name());
      this.StallToMicro.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 0);
      this.TestWakeup = uvm_reg_field::type_id::create("TestWakeup",,get_full_name());
      this.TestWakeup.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.RSVDMicro = uvm_reg_field::type_id::create("RSVDMicro",,get_full_name());
      this.RSVDMicro.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
      this.ResetToMicro = uvm_reg_field::type_id::create("ResetToMicro",,get_full_name());
      this.ResetToMicro.configure(this, 1, 3, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_MicroReset)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_MicroReset


class ral_reg_DWC_DDRPHYA_APBONLY0_MicroResetPIEEn extends uvm_reg;
	rand uvm_reg_field MicroResetPIEEn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   MicroResetPIEEn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_MicroResetPIEEn");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MicroResetPIEEn = uvm_reg_field::type_id::create("MicroResetPIEEn",,get_full_name());
      this.MicroResetPIEEn.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_MicroResetPIEEn)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_MicroResetPIEEn


class ral_reg_DWC_DDRPHYA_APBONLY0_ClearPIEStallToMicro extends uvm_reg;
	rand uvm_reg_field ClearPIEStallToMicro;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ClearPIEStallToMicro: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_ClearPIEStallToMicro");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ClearPIEStallToMicro = uvm_reg_field::type_id::create("ClearPIEStallToMicro",,get_full_name());
      this.ClearPIEStallToMicro.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_ClearPIEStallToMicro)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_ClearPIEStallToMicro


class ral_reg_DWC_DDRPHYA_APBONLY0_PIEMicroStallDelay extends uvm_reg;
	rand uvm_reg_field PIEMicroStallDelay;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PIEMicroStallDelay: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_APBONLY0_PIEMicroStallDelay");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PIEMicroStallDelay = uvm_reg_field::type_id::create("PIEMicroStallDelay",,get_full_name());
      this.PIEMicroStallDelay.configure(this, 4, 0, "RW", 0, 4'h4, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_PIEMicroStallDelay)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_PIEMicroStallDelay


class ral_reg_DWC_DDRPHYA_APBONLY0_SequencerOverride extends uvm_reg;
	rand uvm_reg_field SequencerOverride;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   SequencerOverride: coverpoint {m_data[14:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {16'b??????????????00};
	      wildcard bins bit_0_wr_as_1 = {16'b??????????????10};
	      wildcard bins bit_0_rd_as_0 = {16'b??????????????01};
	      wildcard bins bit_0_rd_as_1 = {16'b??????????????11};
	      wildcard bins bit_1_wr_as_0 = {16'b?????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {16'b?????????????1?0};
	      wildcard bins bit_1_rd_as_0 = {16'b?????????????0?1};
	      wildcard bins bit_1_rd_as_1 = {16'b?????????????1?1};
	      wildcard bins bit_2_wr_as_0 = {16'b????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {16'b????????????1??0};
	      wildcard bins bit_2_rd_as_0 = {16'b????????????0??1};
	      wildcard bins bit_2_rd_as_1 = {16'b????????????1??1};
	      wildcard bins bit_3_wr_as_0 = {16'b???????????0???0};
	      wildcard bins bit_3_wr_as_1 = {16'b???????????1???0};
	      wildcard bins bit_3_rd_as_0 = {16'b???????????0???1};
	      wildcard bins bit_3_rd_as_1 = {16'b???????????1???1};
	      wildcard bins bit_4_wr_as_0 = {16'b??????????0????0};
	      wildcard bins bit_4_wr_as_1 = {16'b??????????1????0};
	      wildcard bins bit_4_rd_as_0 = {16'b??????????0????1};
	      wildcard bins bit_4_rd_as_1 = {16'b??????????1????1};
	      wildcard bins bit_5_wr_as_0 = {16'b?????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {16'b?????????1?????0};
	      wildcard bins bit_5_rd_as_0 = {16'b?????????0?????1};
	      wildcard bins bit_5_rd_as_1 = {16'b?????????1?????1};
	      wildcard bins bit_6_wr_as_0 = {16'b????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {16'b????????1??????0};
	      wildcard bins bit_6_rd_as_0 = {16'b????????0??????1};
	      wildcard bins bit_6_rd_as_1 = {16'b????????1??????1};
	      wildcard bins bit_7_wr_as_0 = {16'b???????0???????0};
	      wildcard bins bit_7_wr_as_1 = {16'b???????1???????0};
	      wildcard bins bit_7_rd_as_0 = {16'b???????0???????1};
	      wildcard bins bit_7_rd_as_1 = {16'b???????1???????1};
	      wildcard bins bit_8_wr_as_0 = {16'b??????0????????0};
	      wildcard bins bit_8_wr_as_1 = {16'b??????1????????0};
	      wildcard bins bit_8_rd_as_0 = {16'b??????0????????1};
	      wildcard bins bit_8_rd_as_1 = {16'b??????1????????1};
	      wildcard bins bit_9_wr_as_0 = {16'b?????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {16'b?????1?????????0};
	      wildcard bins bit_9_rd_as_0 = {16'b?????0?????????1};
	      wildcard bins bit_9_rd_as_1 = {16'b?????1?????????1};
	      wildcard bins bit_10_wr_as_0 = {16'b????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {16'b????1??????????0};
	      wildcard bins bit_10_rd_as_0 = {16'b????0??????????1};
	      wildcard bins bit_10_rd_as_1 = {16'b????1??????????1};
	      wildcard bins bit_11_wr_as_0 = {16'b???0???????????0};
	      wildcard bins bit_11_wr_as_1 = {16'b???1???????????0};
	      wildcard bins bit_11_rd_as_0 = {16'b???0???????????1};
	      wildcard bins bit_11_rd_as_1 = {16'b???1???????????1};
	      wildcard bins bit_12_wr_as_0 = {16'b??0????????????0};
	      wildcard bins bit_12_wr_as_1 = {16'b??1????????????0};
	      wildcard bins bit_12_rd_as_0 = {16'b??0????????????1};
	      wildcard bins bit_12_rd_as_1 = {16'b??1????????????1};
	      wildcard bins bit_13_wr_as_0 = {16'b?0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {16'b?1?????????????0};
	      wildcard bins bit_13_rd_as_0 = {16'b?0?????????????1};
	      wildcard bins bit_13_rd_as_1 = {16'b?1?????????????1};
	      wildcard bins bit_14_wr_as_0 = {16'b0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {16'b1??????????????0};
	      wildcard bins bit_14_rd_as_0 = {16'b0??????????????1};
	      wildcard bins bit_14_rd_as_1 = {16'b1??????????????1};
	      option.weight = 60;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_SequencerOverride");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.SequencerOverride = uvm_reg_field::type_id::create("SequencerOverride",,get_full_name());
      this.SequencerOverride.configure(this, 15, 0, "RW", 0, 15'h80, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_SequencerOverride)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_SequencerOverride


class ral_reg_DWC_DDRPHYA_APBONLY0_DfiInitCompleteShadow extends uvm_reg;
	uvm_reg_field DfiInitCompleteShadow;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiInitCompleteShadow: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0_DfiInitCompleteShadow");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiInitCompleteShadow = uvm_reg_field::type_id::create("DfiInitCompleteShadow",,get_full_name());
      this.DfiInitCompleteShadow.configure(this, 1, 0, "RO", 1, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_DfiInitCompleteShadow)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_DfiInitCompleteShadow


class ral_reg_DWC_DDRPHYA_APBONLY0_APBONLYReserved0 extends uvm_reg;
	rand uvm_reg_field APBONLYReserved0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   APBONLYReserved0: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_APBONLY0_APBONLYReserved0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.APBONLYReserved0 = uvm_reg_field::type_id::create("APBONLYReserved0",,get_full_name());
      this.APBONLYReserved0.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_APBONLY0_APBONLYReserved0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_APBONLY0_APBONLYReserved0


class ral_block_DWC_DDRPHYA_APBONLY0 extends uvm_reg_block;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_MicroContMuxSel MicroContMuxSel;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_ContextToMicro ContextToMicro;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_ExternalAHBReset ExternalAHBReset;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_TDRDisable TDRDisable;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_UctShadowRegs UctShadowRegs;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_BlockDfiShadowRegs BlockDfiShadowRegs;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_CCMWriteBypassEnable CCMWriteBypassEnable;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_DctWriteOnly DctWriteOnly;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_DctWriteProt DctWriteProt;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_UctWriteOnlyShadow UctWriteOnlyShadow;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_UctDatWriteOnlyShadow UctDatWriteOnlyShadow;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_NeverGateCsrClock NeverGateCsrClock;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_NeverGateAcCsrClock NeverGateAcCsrClock;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_DfiCfgRdDataValidTicks DfiCfgRdDataValidTicks;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_DisableHMRdSpeedUp DisableHMRdSpeedUp;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_OverrideHMRdSpeedUp OverrideHMRdSpeedUp;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugControl Dfi0DebugControl;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugCapture0 Dfi0DebugCapture0;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugCapture1 Dfi0DebugCapture1;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugPerfCtrEn Dfi0DebugPerfCtrEn;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugPerfCtr Dfi0DebugPerfCtr;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugControl Dfi1DebugControl;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugCapture0 Dfi1DebugCapture0;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugCapture1 Dfi1DebugCapture1;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugPerfCtrEn Dfi1DebugPerfCtrEn;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugPerfCtr Dfi1DebugPerfCtr;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_APBONLYParityInvert APBONLYParityInvert;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_WaitCondAPB WaitCondAPB;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_PIERdDataValidTicks PIERdDataValidTicks;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_UCRdDataValidTicks UCRdDataValidTicks;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_ScratchPadAPBONLY ScratchPadAPBONLY;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_MicroReset MicroReset;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_MicroResetPIEEn MicroResetPIEEn;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_ClearPIEStallToMicro ClearPIEStallToMicro;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_PIEMicroStallDelay PIEMicroStallDelay;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_SequencerOverride SequencerOverride;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_DfiInitCompleteShadow DfiInitCompleteShadow;
	rand ral_reg_DWC_DDRPHYA_APBONLY0_APBONLYReserved0 APBONLYReserved0;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field MicroContMuxSel_MicroContMuxSel;
	rand uvm_reg_field ContextToMicro_ContextToMicro;
	rand uvm_reg_field ExternalAHBReset_ExternalAHBReset;
	rand uvm_reg_field TDRDisable_TDRDisable;
	uvm_reg_field UctShadowRegs_UctWriteProtShadow;
	uvm_reg_field UctWriteProtShadow;
	uvm_reg_field UctShadowRegs_UctDatWriteProtShadow;
	uvm_reg_field UctDatWriteProtShadow;
	uvm_reg_field BlockDfiShadowRegs_BlockDfiInterfaceEnShadow;
	uvm_reg_field BlockDfiInterfaceEnShadow;
	uvm_reg_field BlockDfiShadowRegs_PmuBusyShadow;
	uvm_reg_field PmuBusyShadow;
	rand uvm_reg_field CCMWriteBypassEnable_CCMWriteBypassEnable;
	rand uvm_reg_field DctWriteOnly_DctWriteOnly;
	rand uvm_reg_field DctWriteProt_DctWriteProt;
	uvm_reg_field UctWriteOnlyShadow_UctWriteOnlyShadow;
	uvm_reg_field UctDatWriteOnlyShadow_UctDatWriteOnlyShadow;
	rand uvm_reg_field NeverGateCsrClock_NeverGateCsrClock;
	rand uvm_reg_field NeverGateAcCsrClock_NeverGateAcCsrClock;
	rand uvm_reg_field DfiCfgRdDataValidTicks_DfiCfgRdDataValidTicksARC;
	rand uvm_reg_field DfiCfgRdDataValidTicksARC;
	rand uvm_reg_field DfiCfgRdDataValidTicks_DfiCfgRdDataValidTicksReg;
	rand uvm_reg_field DfiCfgRdDataValidTicksReg;
	rand uvm_reg_field DisableHMRdSpeedUp_DisableHMRdSpeedUp;
	rand uvm_reg_field OverrideHMRdSpeedUp_OverrideHMRdSpeedUp;
	rand uvm_reg_field Dfi0DebugControl_Dfi0DebugControl;
	uvm_reg_field Dfi0DebugCapture0_Dfi0DebugCapture0;
	uvm_reg_field Dfi0DebugCapture1_Dfi0DebugCapture1;
	rand uvm_reg_field Dfi0DebugPerfCtrEn_Dfi0DebugPerfCtrEn;
	uvm_reg_field Dfi0DebugPerfCtr_Dfi0DebugPerfCtr;
	rand uvm_reg_field Dfi1DebugControl_Dfi1DebugControl;
	uvm_reg_field Dfi1DebugCapture0_Dfi1DebugCapture0;
	uvm_reg_field Dfi1DebugCapture1_Dfi1DebugCapture1;
	rand uvm_reg_field Dfi1DebugPerfCtrEn_Dfi1DebugPerfCtrEn;
	uvm_reg_field Dfi1DebugPerfCtr_Dfi1DebugPerfCtr;
	rand uvm_reg_field APBONLYParityInvert_APBONLYParityInvert;
	rand uvm_reg_field WaitCondAPB_WaitCondAPB;
	rand uvm_reg_field PIERdDataValidTicks_PIERdDataValidTicksARC;
	rand uvm_reg_field PIERdDataValidTicksARC;
	rand uvm_reg_field PIERdDataValidTicks_PIERdDataValidTicksReg;
	rand uvm_reg_field PIERdDataValidTicksReg;
	rand uvm_reg_field UCRdDataValidTicks_UCRdDataValidTicksARC;
	rand uvm_reg_field UCRdDataValidTicksARC;
	rand uvm_reg_field UCRdDataValidTicks_UCRdDataValidTicksReg;
	rand uvm_reg_field UCRdDataValidTicksReg;
	rand uvm_reg_field ScratchPadAPBONLY_ScratchPadAPBONLY;
	rand uvm_reg_field MicroReset_StallToMicro;
	rand uvm_reg_field StallToMicro;
	rand uvm_reg_field MicroReset_TestWakeup;
	rand uvm_reg_field TestWakeup;
	rand uvm_reg_field MicroReset_RSVDMicro;
	rand uvm_reg_field RSVDMicro;
	rand uvm_reg_field MicroReset_ResetToMicro;
	rand uvm_reg_field ResetToMicro;
	rand uvm_reg_field MicroResetPIEEn_MicroResetPIEEn;
	rand uvm_reg_field ClearPIEStallToMicro_ClearPIEStallToMicro;
	rand uvm_reg_field PIEMicroStallDelay_PIEMicroStallDelay;
	rand uvm_reg_field SequencerOverride_SequencerOverride;
	uvm_reg_field DfiInitCompleteShadow_DfiInitCompleteShadow;
	rand uvm_reg_field APBONLYReserved0_APBONLYReserved0;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	MicroContMuxSel : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h0 };
		option.weight = 1;
	}

	ContextToMicro : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1 };
		option.weight = 1;
	}

	ExternalAHBReset : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2 };
		option.weight = 1;
	}

	TDRDisable : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3 };
		option.weight = 1;
	}

	UctShadowRegs : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4 };
		option.weight = 1;
	}

	BlockDfiShadowRegs : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5 };
		option.weight = 1;
	}

	CCMWriteBypassEnable : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h8 };
		option.weight = 1;
	}

	DctWriteOnly : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h30 };
		option.weight = 1;
	}

	DctWriteProt : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h31 };
		option.weight = 1;
	}

	UctWriteOnlyShadow : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h32 };
		option.weight = 1;
	}

	UctDatWriteOnlyShadow : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h34 };
		option.weight = 1;
	}

	NeverGateCsrClock : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h35 };
		option.weight = 1;
	}

	NeverGateAcCsrClock : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h36 };
		option.weight = 1;
	}

	DfiCfgRdDataValidTicks : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h37 };
		option.weight = 1;
	}

	DisableHMRdSpeedUp : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h39 };
		option.weight = 1;
	}

	OverrideHMRdSpeedUp : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3A };
		option.weight = 1;
	}

	Dfi0DebugControl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h40 };
		option.weight = 1;
	}

	Dfi0DebugCapture0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h41 };
		option.weight = 1;
	}

	Dfi0DebugCapture1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h42 };
		option.weight = 1;
	}

	Dfi0DebugPerfCtrEn : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h43 };
		option.weight = 1;
	}

	Dfi0DebugPerfCtr : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h44 };
		option.weight = 1;
	}

	Dfi1DebugControl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h48 };
		option.weight = 1;
	}

	Dfi1DebugCapture0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h49 };
		option.weight = 1;
	}

	Dfi1DebugCapture1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4A };
		option.weight = 1;
	}

	Dfi1DebugPerfCtrEn : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4B };
		option.weight = 1;
	}

	Dfi1DebugPerfCtr : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4C };
		option.weight = 1;
	}

	APBONLYParityInvert : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4D };
		option.weight = 1;
	}

	WaitCondAPB : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h50 };
		option.weight = 1;
	}

	PIERdDataValidTicks : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h51 };
		option.weight = 1;
	}

	UCRdDataValidTicks : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h52 };
		option.weight = 1;
	}

	ScratchPadAPBONLY : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h7D };
		option.weight = 1;
	}

	MicroReset : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h99 };
		option.weight = 1;
	}

	MicroResetPIEEn : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h9A };
		option.weight = 1;
	}

	ClearPIEStallToMicro : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h9B };
		option.weight = 1;
	}

	PIEMicroStallDelay : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h9C };
		option.weight = 1;
	}

	SequencerOverride : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hE7 };
		option.weight = 1;
	}

	DfiInitCompleteShadow : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFA };
		option.weight = 1;
	}

	APBONLYReserved0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFD };
		option.weight = 1;
	}
endgroup
	function new(string name = "DWC_DDRPHYA_APBONLY0");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.MicroContMuxSel = ral_reg_DWC_DDRPHYA_APBONLY0_MicroContMuxSel::type_id::create("MicroContMuxSel",,get_full_name());
      if(this.MicroContMuxSel.has_coverage(UVM_CVR_ALL))
      	this.MicroContMuxSel.cg_bits.option.name = {get_name(), ".", "MicroContMuxSel_bits"};
      this.MicroContMuxSel.configure(this, null, "");
      this.MicroContMuxSel.build();
      this.default_map.add_reg(this.MicroContMuxSel, `UVM_REG_ADDR_WIDTH'h0, "RW", 0);
		this.MicroContMuxSel_MicroContMuxSel = this.MicroContMuxSel.MicroContMuxSel;
      this.ContextToMicro = ral_reg_DWC_DDRPHYA_APBONLY0_ContextToMicro::type_id::create("ContextToMicro",,get_full_name());
      if(this.ContextToMicro.has_coverage(UVM_CVR_ALL))
      	this.ContextToMicro.cg_bits.option.name = {get_name(), ".", "ContextToMicro_bits"};
      this.ContextToMicro.configure(this, null, "");
      this.ContextToMicro.build();
      this.default_map.add_reg(this.ContextToMicro, `UVM_REG_ADDR_WIDTH'h1, "RW", 0);
		this.ContextToMicro_ContextToMicro = this.ContextToMicro.ContextToMicro;
      this.ExternalAHBReset = ral_reg_DWC_DDRPHYA_APBONLY0_ExternalAHBReset::type_id::create("ExternalAHBReset",,get_full_name());
      if(this.ExternalAHBReset.has_coverage(UVM_CVR_ALL))
      	this.ExternalAHBReset.cg_bits.option.name = {get_name(), ".", "ExternalAHBReset_bits"};
      this.ExternalAHBReset.configure(this, null, "");
      this.ExternalAHBReset.build();
      this.default_map.add_reg(this.ExternalAHBReset, `UVM_REG_ADDR_WIDTH'h2, "RW", 0);
		this.ExternalAHBReset_ExternalAHBReset = this.ExternalAHBReset.ExternalAHBReset;
      this.TDRDisable = ral_reg_DWC_DDRPHYA_APBONLY0_TDRDisable::type_id::create("TDRDisable",,get_full_name());
      if(this.TDRDisable.has_coverage(UVM_CVR_ALL))
      	this.TDRDisable.cg_bits.option.name = {get_name(), ".", "TDRDisable_bits"};
      this.TDRDisable.configure(this, null, "");
      this.TDRDisable.build();
      this.default_map.add_reg(this.TDRDisable, `UVM_REG_ADDR_WIDTH'h3, "RW", 0);
		this.TDRDisable_TDRDisable = this.TDRDisable.TDRDisable;
      this.UctShadowRegs = ral_reg_DWC_DDRPHYA_APBONLY0_UctShadowRegs::type_id::create("UctShadowRegs",,get_full_name());
      if(this.UctShadowRegs.has_coverage(UVM_CVR_ALL))
      	this.UctShadowRegs.cg_bits.option.name = {get_name(), ".", "UctShadowRegs_bits"};
      this.UctShadowRegs.configure(this, null, "");
      this.UctShadowRegs.build();
      this.default_map.add_reg(this.UctShadowRegs, `UVM_REG_ADDR_WIDTH'h4, "RO", 0);
		this.UctShadowRegs_UctWriteProtShadow = this.UctShadowRegs.UctWriteProtShadow;
		this.UctWriteProtShadow = this.UctShadowRegs.UctWriteProtShadow;
		this.UctShadowRegs_UctDatWriteProtShadow = this.UctShadowRegs.UctDatWriteProtShadow;
		this.UctDatWriteProtShadow = this.UctShadowRegs.UctDatWriteProtShadow;
      this.BlockDfiShadowRegs = ral_reg_DWC_DDRPHYA_APBONLY0_BlockDfiShadowRegs::type_id::create("BlockDfiShadowRegs",,get_full_name());
      if(this.BlockDfiShadowRegs.has_coverage(UVM_CVR_ALL))
      	this.BlockDfiShadowRegs.cg_bits.option.name = {get_name(), ".", "BlockDfiShadowRegs_bits"};
      this.BlockDfiShadowRegs.configure(this, null, "");
      this.BlockDfiShadowRegs.build();
      this.default_map.add_reg(this.BlockDfiShadowRegs, `UVM_REG_ADDR_WIDTH'h5, "RO", 0);
		this.BlockDfiShadowRegs_BlockDfiInterfaceEnShadow = this.BlockDfiShadowRegs.BlockDfiInterfaceEnShadow;
		this.BlockDfiInterfaceEnShadow = this.BlockDfiShadowRegs.BlockDfiInterfaceEnShadow;
		this.BlockDfiShadowRegs_PmuBusyShadow = this.BlockDfiShadowRegs.PmuBusyShadow;
		this.PmuBusyShadow = this.BlockDfiShadowRegs.PmuBusyShadow;
      this.CCMWriteBypassEnable = ral_reg_DWC_DDRPHYA_APBONLY0_CCMWriteBypassEnable::type_id::create("CCMWriteBypassEnable",,get_full_name());
      if(this.CCMWriteBypassEnable.has_coverage(UVM_CVR_ALL))
      	this.CCMWriteBypassEnable.cg_bits.option.name = {get_name(), ".", "CCMWriteBypassEnable_bits"};
      this.CCMWriteBypassEnable.configure(this, null, "");
      this.CCMWriteBypassEnable.build();
      this.default_map.add_reg(this.CCMWriteBypassEnable, `UVM_REG_ADDR_WIDTH'h8, "RW", 0);
		this.CCMWriteBypassEnable_CCMWriteBypassEnable = this.CCMWriteBypassEnable.CCMWriteBypassEnable;
      this.DctWriteOnly = ral_reg_DWC_DDRPHYA_APBONLY0_DctWriteOnly::type_id::create("DctWriteOnly",,get_full_name());
      if(this.DctWriteOnly.has_coverage(UVM_CVR_ALL))
      	this.DctWriteOnly.cg_bits.option.name = {get_name(), ".", "DctWriteOnly_bits"};
      this.DctWriteOnly.configure(this, null, "");
      this.DctWriteOnly.build();
      this.default_map.add_reg(this.DctWriteOnly, `UVM_REG_ADDR_WIDTH'h30, "RW", 0);
		this.DctWriteOnly_DctWriteOnly = this.DctWriteOnly.DctWriteOnly;
      this.DctWriteProt = ral_reg_DWC_DDRPHYA_APBONLY0_DctWriteProt::type_id::create("DctWriteProt",,get_full_name());
      if(this.DctWriteProt.has_coverage(UVM_CVR_ALL))
      	this.DctWriteProt.cg_bits.option.name = {get_name(), ".", "DctWriteProt_bits"};
      this.DctWriteProt.configure(this, null, "");
      this.DctWriteProt.build();
      this.default_map.add_reg(this.DctWriteProt, `UVM_REG_ADDR_WIDTH'h31, "RW", 0);
		this.DctWriteProt_DctWriteProt = this.DctWriteProt.DctWriteProt;
      this.UctWriteOnlyShadow = ral_reg_DWC_DDRPHYA_APBONLY0_UctWriteOnlyShadow::type_id::create("UctWriteOnlyShadow",,get_full_name());
      if(this.UctWriteOnlyShadow.has_coverage(UVM_CVR_ALL))
      	this.UctWriteOnlyShadow.cg_bits.option.name = {get_name(), ".", "UctWriteOnlyShadow_bits"};
      this.UctWriteOnlyShadow.configure(this, null, "");
      this.UctWriteOnlyShadow.build();
      this.default_map.add_reg(this.UctWriteOnlyShadow, `UVM_REG_ADDR_WIDTH'h32, "RO", 0);
		this.UctWriteOnlyShadow_UctWriteOnlyShadow = this.UctWriteOnlyShadow.UctWriteOnlyShadow;
      this.UctDatWriteOnlyShadow = ral_reg_DWC_DDRPHYA_APBONLY0_UctDatWriteOnlyShadow::type_id::create("UctDatWriteOnlyShadow",,get_full_name());
      if(this.UctDatWriteOnlyShadow.has_coverage(UVM_CVR_ALL))
      	this.UctDatWriteOnlyShadow.cg_bits.option.name = {get_name(), ".", "UctDatWriteOnlyShadow_bits"};
      this.UctDatWriteOnlyShadow.configure(this, null, "");
      this.UctDatWriteOnlyShadow.build();
      this.default_map.add_reg(this.UctDatWriteOnlyShadow, `UVM_REG_ADDR_WIDTH'h34, "RO", 0);
		this.UctDatWriteOnlyShadow_UctDatWriteOnlyShadow = this.UctDatWriteOnlyShadow.UctDatWriteOnlyShadow;
      this.NeverGateCsrClock = ral_reg_DWC_DDRPHYA_APBONLY0_NeverGateCsrClock::type_id::create("NeverGateCsrClock",,get_full_name());
      if(this.NeverGateCsrClock.has_coverage(UVM_CVR_ALL))
      	this.NeverGateCsrClock.cg_bits.option.name = {get_name(), ".", "NeverGateCsrClock_bits"};
      this.NeverGateCsrClock.configure(this, null, "");
      this.NeverGateCsrClock.build();
      this.default_map.add_reg(this.NeverGateCsrClock, `UVM_REG_ADDR_WIDTH'h35, "RW", 0);
		this.NeverGateCsrClock_NeverGateCsrClock = this.NeverGateCsrClock.NeverGateCsrClock;
      this.NeverGateAcCsrClock = ral_reg_DWC_DDRPHYA_APBONLY0_NeverGateAcCsrClock::type_id::create("NeverGateAcCsrClock",,get_full_name());
      if(this.NeverGateAcCsrClock.has_coverage(UVM_CVR_ALL))
      	this.NeverGateAcCsrClock.cg_bits.option.name = {get_name(), ".", "NeverGateAcCsrClock_bits"};
      this.NeverGateAcCsrClock.configure(this, null, "");
      this.NeverGateAcCsrClock.build();
      this.default_map.add_reg(this.NeverGateAcCsrClock, `UVM_REG_ADDR_WIDTH'h36, "RW", 0);
		this.NeverGateAcCsrClock_NeverGateAcCsrClock = this.NeverGateAcCsrClock.NeverGateAcCsrClock;
      this.DfiCfgRdDataValidTicks = ral_reg_DWC_DDRPHYA_APBONLY0_DfiCfgRdDataValidTicks::type_id::create("DfiCfgRdDataValidTicks",,get_full_name());
      if(this.DfiCfgRdDataValidTicks.has_coverage(UVM_CVR_ALL))
      	this.DfiCfgRdDataValidTicks.cg_bits.option.name = {get_name(), ".", "DfiCfgRdDataValidTicks_bits"};
      this.DfiCfgRdDataValidTicks.configure(this, null, "");
      this.DfiCfgRdDataValidTicks.build();
      this.default_map.add_reg(this.DfiCfgRdDataValidTicks, `UVM_REG_ADDR_WIDTH'h37, "RW", 0);
		this.DfiCfgRdDataValidTicks_DfiCfgRdDataValidTicksARC = this.DfiCfgRdDataValidTicks.DfiCfgRdDataValidTicksARC;
		this.DfiCfgRdDataValidTicksARC = this.DfiCfgRdDataValidTicks.DfiCfgRdDataValidTicksARC;
		this.DfiCfgRdDataValidTicks_DfiCfgRdDataValidTicksReg = this.DfiCfgRdDataValidTicks.DfiCfgRdDataValidTicksReg;
		this.DfiCfgRdDataValidTicksReg = this.DfiCfgRdDataValidTicks.DfiCfgRdDataValidTicksReg;
      this.DisableHMRdSpeedUp = ral_reg_DWC_DDRPHYA_APBONLY0_DisableHMRdSpeedUp::type_id::create("DisableHMRdSpeedUp",,get_full_name());
      if(this.DisableHMRdSpeedUp.has_coverage(UVM_CVR_ALL))
      	this.DisableHMRdSpeedUp.cg_bits.option.name = {get_name(), ".", "DisableHMRdSpeedUp_bits"};
      this.DisableHMRdSpeedUp.configure(this, null, "");
      this.DisableHMRdSpeedUp.build();
      this.default_map.add_reg(this.DisableHMRdSpeedUp, `UVM_REG_ADDR_WIDTH'h39, "RW", 0);
		this.DisableHMRdSpeedUp_DisableHMRdSpeedUp = this.DisableHMRdSpeedUp.DisableHMRdSpeedUp;
      this.OverrideHMRdSpeedUp = ral_reg_DWC_DDRPHYA_APBONLY0_OverrideHMRdSpeedUp::type_id::create("OverrideHMRdSpeedUp",,get_full_name());
      if(this.OverrideHMRdSpeedUp.has_coverage(UVM_CVR_ALL))
      	this.OverrideHMRdSpeedUp.cg_bits.option.name = {get_name(), ".", "OverrideHMRdSpeedUp_bits"};
      this.OverrideHMRdSpeedUp.configure(this, null, "");
      this.OverrideHMRdSpeedUp.build();
      this.default_map.add_reg(this.OverrideHMRdSpeedUp, `UVM_REG_ADDR_WIDTH'h3A, "RW", 0);
		this.OverrideHMRdSpeedUp_OverrideHMRdSpeedUp = this.OverrideHMRdSpeedUp.OverrideHMRdSpeedUp;
      this.Dfi0DebugControl = ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugControl::type_id::create("Dfi0DebugControl",,get_full_name());
      if(this.Dfi0DebugControl.has_coverage(UVM_CVR_ALL))
      	this.Dfi0DebugControl.cg_bits.option.name = {get_name(), ".", "Dfi0DebugControl_bits"};
      this.Dfi0DebugControl.configure(this, null, "");
      this.Dfi0DebugControl.build();
      this.default_map.add_reg(this.Dfi0DebugControl, `UVM_REG_ADDR_WIDTH'h40, "RW", 0);
		this.Dfi0DebugControl_Dfi0DebugControl = this.Dfi0DebugControl.Dfi0DebugControl;
      this.Dfi0DebugCapture0 = ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugCapture0::type_id::create("Dfi0DebugCapture0",,get_full_name());
      if(this.Dfi0DebugCapture0.has_coverage(UVM_CVR_ALL))
      	this.Dfi0DebugCapture0.cg_bits.option.name = {get_name(), ".", "Dfi0DebugCapture0_bits"};
      this.Dfi0DebugCapture0.configure(this, null, "");
      this.Dfi0DebugCapture0.build();
      this.default_map.add_reg(this.Dfi0DebugCapture0, `UVM_REG_ADDR_WIDTH'h41, "RO", 0);
		this.Dfi0DebugCapture0_Dfi0DebugCapture0 = this.Dfi0DebugCapture0.Dfi0DebugCapture0;
      this.Dfi0DebugCapture1 = ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugCapture1::type_id::create("Dfi0DebugCapture1",,get_full_name());
      if(this.Dfi0DebugCapture1.has_coverage(UVM_CVR_ALL))
      	this.Dfi0DebugCapture1.cg_bits.option.name = {get_name(), ".", "Dfi0DebugCapture1_bits"};
      this.Dfi0DebugCapture1.configure(this, null, "");
      this.Dfi0DebugCapture1.build();
      this.default_map.add_reg(this.Dfi0DebugCapture1, `UVM_REG_ADDR_WIDTH'h42, "RO", 0);
		this.Dfi0DebugCapture1_Dfi0DebugCapture1 = this.Dfi0DebugCapture1.Dfi0DebugCapture1;
      this.Dfi0DebugPerfCtrEn = ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugPerfCtrEn::type_id::create("Dfi0DebugPerfCtrEn",,get_full_name());
      if(this.Dfi0DebugPerfCtrEn.has_coverage(UVM_CVR_ALL))
      	this.Dfi0DebugPerfCtrEn.cg_bits.option.name = {get_name(), ".", "Dfi0DebugPerfCtrEn_bits"};
      this.Dfi0DebugPerfCtrEn.configure(this, null, "");
      this.Dfi0DebugPerfCtrEn.build();
      this.default_map.add_reg(this.Dfi0DebugPerfCtrEn, `UVM_REG_ADDR_WIDTH'h43, "RW", 0);
		this.Dfi0DebugPerfCtrEn_Dfi0DebugPerfCtrEn = this.Dfi0DebugPerfCtrEn.Dfi0DebugPerfCtrEn;
      this.Dfi0DebugPerfCtr = ral_reg_DWC_DDRPHYA_APBONLY0_Dfi0DebugPerfCtr::type_id::create("Dfi0DebugPerfCtr",,get_full_name());
      if(this.Dfi0DebugPerfCtr.has_coverage(UVM_CVR_ALL))
      	this.Dfi0DebugPerfCtr.cg_bits.option.name = {get_name(), ".", "Dfi0DebugPerfCtr_bits"};
      this.Dfi0DebugPerfCtr.configure(this, null, "");
      this.Dfi0DebugPerfCtr.build();
      this.default_map.add_reg(this.Dfi0DebugPerfCtr, `UVM_REG_ADDR_WIDTH'h44, "RO", 0);
		this.Dfi0DebugPerfCtr_Dfi0DebugPerfCtr = this.Dfi0DebugPerfCtr.Dfi0DebugPerfCtr;
      this.Dfi1DebugControl = ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugControl::type_id::create("Dfi1DebugControl",,get_full_name());
      if(this.Dfi1DebugControl.has_coverage(UVM_CVR_ALL))
      	this.Dfi1DebugControl.cg_bits.option.name = {get_name(), ".", "Dfi1DebugControl_bits"};
      this.Dfi1DebugControl.configure(this, null, "");
      this.Dfi1DebugControl.build();
      this.default_map.add_reg(this.Dfi1DebugControl, `UVM_REG_ADDR_WIDTH'h48, "RW", 0);
		this.Dfi1DebugControl_Dfi1DebugControl = this.Dfi1DebugControl.Dfi1DebugControl;
      this.Dfi1DebugCapture0 = ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugCapture0::type_id::create("Dfi1DebugCapture0",,get_full_name());
      if(this.Dfi1DebugCapture0.has_coverage(UVM_CVR_ALL))
      	this.Dfi1DebugCapture0.cg_bits.option.name = {get_name(), ".", "Dfi1DebugCapture0_bits"};
      this.Dfi1DebugCapture0.configure(this, null, "");
      this.Dfi1DebugCapture0.build();
      this.default_map.add_reg(this.Dfi1DebugCapture0, `UVM_REG_ADDR_WIDTH'h49, "RO", 0);
		this.Dfi1DebugCapture0_Dfi1DebugCapture0 = this.Dfi1DebugCapture0.Dfi1DebugCapture0;
      this.Dfi1DebugCapture1 = ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugCapture1::type_id::create("Dfi1DebugCapture1",,get_full_name());
      if(this.Dfi1DebugCapture1.has_coverage(UVM_CVR_ALL))
      	this.Dfi1DebugCapture1.cg_bits.option.name = {get_name(), ".", "Dfi1DebugCapture1_bits"};
      this.Dfi1DebugCapture1.configure(this, null, "");
      this.Dfi1DebugCapture1.build();
      this.default_map.add_reg(this.Dfi1DebugCapture1, `UVM_REG_ADDR_WIDTH'h4A, "RO", 0);
		this.Dfi1DebugCapture1_Dfi1DebugCapture1 = this.Dfi1DebugCapture1.Dfi1DebugCapture1;
      this.Dfi1DebugPerfCtrEn = ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugPerfCtrEn::type_id::create("Dfi1DebugPerfCtrEn",,get_full_name());
      if(this.Dfi1DebugPerfCtrEn.has_coverage(UVM_CVR_ALL))
      	this.Dfi1DebugPerfCtrEn.cg_bits.option.name = {get_name(), ".", "Dfi1DebugPerfCtrEn_bits"};
      this.Dfi1DebugPerfCtrEn.configure(this, null, "");
      this.Dfi1DebugPerfCtrEn.build();
      this.default_map.add_reg(this.Dfi1DebugPerfCtrEn, `UVM_REG_ADDR_WIDTH'h4B, "RW", 0);
		this.Dfi1DebugPerfCtrEn_Dfi1DebugPerfCtrEn = this.Dfi1DebugPerfCtrEn.Dfi1DebugPerfCtrEn;
      this.Dfi1DebugPerfCtr = ral_reg_DWC_DDRPHYA_APBONLY0_Dfi1DebugPerfCtr::type_id::create("Dfi1DebugPerfCtr",,get_full_name());
      if(this.Dfi1DebugPerfCtr.has_coverage(UVM_CVR_ALL))
      	this.Dfi1DebugPerfCtr.cg_bits.option.name = {get_name(), ".", "Dfi1DebugPerfCtr_bits"};
      this.Dfi1DebugPerfCtr.configure(this, null, "");
      this.Dfi1DebugPerfCtr.build();
      this.default_map.add_reg(this.Dfi1DebugPerfCtr, `UVM_REG_ADDR_WIDTH'h4C, "RO", 0);
		this.Dfi1DebugPerfCtr_Dfi1DebugPerfCtr = this.Dfi1DebugPerfCtr.Dfi1DebugPerfCtr;
      this.APBONLYParityInvert = ral_reg_DWC_DDRPHYA_APBONLY0_APBONLYParityInvert::type_id::create("APBONLYParityInvert",,get_full_name());
      if(this.APBONLYParityInvert.has_coverage(UVM_CVR_ALL))
      	this.APBONLYParityInvert.cg_bits.option.name = {get_name(), ".", "APBONLYParityInvert_bits"};
      this.APBONLYParityInvert.configure(this, null, "");
      this.APBONLYParityInvert.build();
      this.default_map.add_reg(this.APBONLYParityInvert, `UVM_REG_ADDR_WIDTH'h4D, "RW", 0);
		this.APBONLYParityInvert_APBONLYParityInvert = this.APBONLYParityInvert.APBONLYParityInvert;
      this.WaitCondAPB = ral_reg_DWC_DDRPHYA_APBONLY0_WaitCondAPB::type_id::create("WaitCondAPB",,get_full_name());
      if(this.WaitCondAPB.has_coverage(UVM_CVR_ALL))
      	this.WaitCondAPB.cg_bits.option.name = {get_name(), ".", "WaitCondAPB_bits"};
      this.WaitCondAPB.configure(this, null, "");
      this.WaitCondAPB.build();
      this.default_map.add_reg(this.WaitCondAPB, `UVM_REG_ADDR_WIDTH'h50, "RW", 0);
		this.WaitCondAPB_WaitCondAPB = this.WaitCondAPB.WaitCondAPB;
      this.PIERdDataValidTicks = ral_reg_DWC_DDRPHYA_APBONLY0_PIERdDataValidTicks::type_id::create("PIERdDataValidTicks",,get_full_name());
      if(this.PIERdDataValidTicks.has_coverage(UVM_CVR_ALL))
      	this.PIERdDataValidTicks.cg_bits.option.name = {get_name(), ".", "PIERdDataValidTicks_bits"};
      this.PIERdDataValidTicks.configure(this, null, "");
      this.PIERdDataValidTicks.build();
      this.default_map.add_reg(this.PIERdDataValidTicks, `UVM_REG_ADDR_WIDTH'h51, "RW", 0);
		this.PIERdDataValidTicks_PIERdDataValidTicksARC = this.PIERdDataValidTicks.PIERdDataValidTicksARC;
		this.PIERdDataValidTicksARC = this.PIERdDataValidTicks.PIERdDataValidTicksARC;
		this.PIERdDataValidTicks_PIERdDataValidTicksReg = this.PIERdDataValidTicks.PIERdDataValidTicksReg;
		this.PIERdDataValidTicksReg = this.PIERdDataValidTicks.PIERdDataValidTicksReg;
      this.UCRdDataValidTicks = ral_reg_DWC_DDRPHYA_APBONLY0_UCRdDataValidTicks::type_id::create("UCRdDataValidTicks",,get_full_name());
      if(this.UCRdDataValidTicks.has_coverage(UVM_CVR_ALL))
      	this.UCRdDataValidTicks.cg_bits.option.name = {get_name(), ".", "UCRdDataValidTicks_bits"};
      this.UCRdDataValidTicks.configure(this, null, "");
      this.UCRdDataValidTicks.build();
      this.default_map.add_reg(this.UCRdDataValidTicks, `UVM_REG_ADDR_WIDTH'h52, "RW", 0);
		this.UCRdDataValidTicks_UCRdDataValidTicksARC = this.UCRdDataValidTicks.UCRdDataValidTicksARC;
		this.UCRdDataValidTicksARC = this.UCRdDataValidTicks.UCRdDataValidTicksARC;
		this.UCRdDataValidTicks_UCRdDataValidTicksReg = this.UCRdDataValidTicks.UCRdDataValidTicksReg;
		this.UCRdDataValidTicksReg = this.UCRdDataValidTicks.UCRdDataValidTicksReg;
      this.ScratchPadAPBONLY = ral_reg_DWC_DDRPHYA_APBONLY0_ScratchPadAPBONLY::type_id::create("ScratchPadAPBONLY",,get_full_name());
      if(this.ScratchPadAPBONLY.has_coverage(UVM_CVR_ALL))
      	this.ScratchPadAPBONLY.cg_bits.option.name = {get_name(), ".", "ScratchPadAPBONLY_bits"};
      this.ScratchPadAPBONLY.configure(this, null, "");
      this.ScratchPadAPBONLY.build();
      this.default_map.add_reg(this.ScratchPadAPBONLY, `UVM_REG_ADDR_WIDTH'h7D, "RW", 0);
		this.ScratchPadAPBONLY_ScratchPadAPBONLY = this.ScratchPadAPBONLY.ScratchPadAPBONLY;
      this.MicroReset = ral_reg_DWC_DDRPHYA_APBONLY0_MicroReset::type_id::create("MicroReset",,get_full_name());
      if(this.MicroReset.has_coverage(UVM_CVR_ALL))
      	this.MicroReset.cg_bits.option.name = {get_name(), ".", "MicroReset_bits"};
      this.MicroReset.configure(this, null, "");
      this.MicroReset.build();
      this.default_map.add_reg(this.MicroReset, `UVM_REG_ADDR_WIDTH'h99, "RW", 0);
		this.MicroReset_StallToMicro = this.MicroReset.StallToMicro;
		this.StallToMicro = this.MicroReset.StallToMicro;
		this.MicroReset_TestWakeup = this.MicroReset.TestWakeup;
		this.TestWakeup = this.MicroReset.TestWakeup;
		this.MicroReset_RSVDMicro = this.MicroReset.RSVDMicro;
		this.RSVDMicro = this.MicroReset.RSVDMicro;
		this.MicroReset_ResetToMicro = this.MicroReset.ResetToMicro;
		this.ResetToMicro = this.MicroReset.ResetToMicro;
      this.MicroResetPIEEn = ral_reg_DWC_DDRPHYA_APBONLY0_MicroResetPIEEn::type_id::create("MicroResetPIEEn",,get_full_name());
      if(this.MicroResetPIEEn.has_coverage(UVM_CVR_ALL))
      	this.MicroResetPIEEn.cg_bits.option.name = {get_name(), ".", "MicroResetPIEEn_bits"};
      this.MicroResetPIEEn.configure(this, null, "");
      this.MicroResetPIEEn.build();
      this.default_map.add_reg(this.MicroResetPIEEn, `UVM_REG_ADDR_WIDTH'h9A, "RW", 0);
		this.MicroResetPIEEn_MicroResetPIEEn = this.MicroResetPIEEn.MicroResetPIEEn;
      this.ClearPIEStallToMicro = ral_reg_DWC_DDRPHYA_APBONLY0_ClearPIEStallToMicro::type_id::create("ClearPIEStallToMicro",,get_full_name());
      if(this.ClearPIEStallToMicro.has_coverage(UVM_CVR_ALL))
      	this.ClearPIEStallToMicro.cg_bits.option.name = {get_name(), ".", "ClearPIEStallToMicro_bits"};
      this.ClearPIEStallToMicro.configure(this, null, "");
      this.ClearPIEStallToMicro.build();
      this.default_map.add_reg(this.ClearPIEStallToMicro, `UVM_REG_ADDR_WIDTH'h9B, "RW", 0);
		this.ClearPIEStallToMicro_ClearPIEStallToMicro = this.ClearPIEStallToMicro.ClearPIEStallToMicro;
      this.PIEMicroStallDelay = ral_reg_DWC_DDRPHYA_APBONLY0_PIEMicroStallDelay::type_id::create("PIEMicroStallDelay",,get_full_name());
      if(this.PIEMicroStallDelay.has_coverage(UVM_CVR_ALL))
      	this.PIEMicroStallDelay.cg_bits.option.name = {get_name(), ".", "PIEMicroStallDelay_bits"};
      this.PIEMicroStallDelay.configure(this, null, "");
      this.PIEMicroStallDelay.build();
      this.default_map.add_reg(this.PIEMicroStallDelay, `UVM_REG_ADDR_WIDTH'h9C, "RW", 0);
		this.PIEMicroStallDelay_PIEMicroStallDelay = this.PIEMicroStallDelay.PIEMicroStallDelay;
      this.SequencerOverride = ral_reg_DWC_DDRPHYA_APBONLY0_SequencerOverride::type_id::create("SequencerOverride",,get_full_name());
      if(this.SequencerOverride.has_coverage(UVM_CVR_ALL))
      	this.SequencerOverride.cg_bits.option.name = {get_name(), ".", "SequencerOverride_bits"};
      this.SequencerOverride.configure(this, null, "");
      this.SequencerOverride.build();
      this.default_map.add_reg(this.SequencerOverride, `UVM_REG_ADDR_WIDTH'hE7, "RW", 0);
		this.SequencerOverride_SequencerOverride = this.SequencerOverride.SequencerOverride;
      this.DfiInitCompleteShadow = ral_reg_DWC_DDRPHYA_APBONLY0_DfiInitCompleteShadow::type_id::create("DfiInitCompleteShadow",,get_full_name());
      if(this.DfiInitCompleteShadow.has_coverage(UVM_CVR_ALL))
      	this.DfiInitCompleteShadow.cg_bits.option.name = {get_name(), ".", "DfiInitCompleteShadow_bits"};
      this.DfiInitCompleteShadow.configure(this, null, "");
      this.DfiInitCompleteShadow.build();
      this.default_map.add_reg(this.DfiInitCompleteShadow, `UVM_REG_ADDR_WIDTH'hFA, "RO", 0);
		this.DfiInitCompleteShadow_DfiInitCompleteShadow = this.DfiInitCompleteShadow.DfiInitCompleteShadow;
      this.APBONLYReserved0 = ral_reg_DWC_DDRPHYA_APBONLY0_APBONLYReserved0::type_id::create("APBONLYReserved0",,get_full_name());
      if(this.APBONLYReserved0.has_coverage(UVM_CVR_ALL))
      	this.APBONLYReserved0.cg_bits.option.name = {get_name(), ".", "APBONLYReserved0_bits"};
      this.APBONLYReserved0.configure(this, null, "");
      this.APBONLYReserved0.build();
      this.default_map.add_reg(this.APBONLYReserved0, `UVM_REG_ADDR_WIDTH'hFD, "RW", 0);
		this.APBONLYReserved0_APBONLYReserved0 = this.APBONLYReserved0.APBONLYReserved0;
   endfunction : build

	`uvm_object_utils(ral_block_DWC_DDRPHYA_APBONLY0)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_DDRPHYA_APBONLY0


endpackage
`endif
