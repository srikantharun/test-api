`ifndef RAL_DWC_DDRPHYA_HMZCAL0_P3_PKG
`define RAL_DWC_DDRPHYA_HMZCAL0_P3_PKG

package ral_DWC_DDRPHYA_HMZCAL0_p3_pkg;
import uvm_pkg::*;

class ral_reg_DWC_DDRPHYA_HMZCAL0_p3_RxDfeModeCfg_p3 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p3_RxDfeModeCfg_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDfeCtrl = uvm_reg_field::type_id::create("RxDfeCtrl",,get_full_name());
      this.RxDfeCtrl.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p3_RxDfeModeCfg_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p3_RxDfeModeCfg_p3


class ral_reg_DWC_DDRPHYA_HMZCAL0_p3_HMReservedP1_p3 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p3_HMReservedP1_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMReservedP1_p3 = uvm_reg_field::type_id::create("HMReservedP1_p3",,get_full_name());
      this.HMReservedP1_p3.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p3_HMReservedP1_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p3_HMReservedP1_p3


class ral_reg_DWC_DDRPHYA_HMZCAL0_p3_ZCalCompCtrl_p3 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p3_ZCalCompCtrl_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalCompGainCurrAdj = uvm_reg_field::type_id::create("ZCalCompGainCurrAdj",,get_full_name());
      this.ZCalCompGainCurrAdj.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p3_ZCalCompCtrl_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p3_ZCalCompCtrl_p3


class ral_reg_DWC_DDRPHYA_HMZCAL0_p3_ZCalSlewRateCtrl_p3 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p3_ZCalSlewRateCtrl_p3");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p3_ZCalSlewRateCtrl_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p3_ZCalSlewRateCtrl_p3


class ral_reg_DWC_DDRPHYA_HMZCAL0_p3_TxSeg120_p3 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p3_TxSeg120_p3");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p3_TxSeg120_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p3_TxSeg120_p3


class ral_reg_DWC_DDRPHYA_HMZCAL0_p3_RxVrefDac_p3 extends uvm_reg;
	rand uvm_reg_field RxVrefDac_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxVrefDac_p3: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p3_RxVrefDac_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxVrefDac_p3 = uvm_reg_field::type_id::create("RxVrefDac_p3",,get_full_name());
      this.RxVrefDac_p3.configure(this, 9, 0, "RW", 0, 9'hff, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p3_RxVrefDac_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p3_RxVrefDac_p3


class ral_reg_DWC_DDRPHYA_HMZCAL0_p3_OdtSeg120_p3 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p3_OdtSeg120_p3");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p3_OdtSeg120_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p3_OdtSeg120_p3


class ral_reg_DWC_DDRPHYA_HMZCAL0_p3_ReservedPZCAL_p3 extends uvm_reg;
	rand uvm_reg_field ReservedPZCAL_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ReservedPZCAL_p3: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p3_ReservedPZCAL_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ReservedPZCAL_p3 = uvm_reg_field::type_id::create("ReservedPZCAL_p3",,get_full_name());
      this.ReservedPZCAL_p3.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMZCAL0_p3_ReservedPZCAL_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMZCAL0_p3_ReservedPZCAL_p3


class ral_block_DWC_DDRPHYA_HMZCAL0_p3 extends uvm_reg_block;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p3_RxDfeModeCfg_p3 RxDfeModeCfg_p3;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p3_HMReservedP1_p3 HMReservedP1_p3;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p3_ZCalCompCtrl_p3 ZCalCompCtrl_p3;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p3_ZCalSlewRateCtrl_p3 ZCalSlewRateCtrl_p3;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p3_TxSeg120_p3 TxSeg120_p3;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p3_RxVrefDac_p3 RxVrefDac_p3;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p3_OdtSeg120_p3 OdtSeg120_p3;
	rand ral_reg_DWC_DDRPHYA_HMZCAL0_p3_ReservedPZCAL_p3 ReservedPZCAL_p3;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field RxDfeModeCfg_p3_RxDfeCtrl;
	rand uvm_reg_field RxDfeCtrl;
	rand uvm_reg_field HMReservedP1_p3_HMReservedP1_p3;
	rand uvm_reg_field ZCalCompCtrl_p3_ZCalCompGainCurrAdj;
	rand uvm_reg_field ZCalCompGainCurrAdj;
	rand uvm_reg_field ZCalSlewRateCtrl_p3_ZCalTxSlewPU;
	rand uvm_reg_field ZCalTxSlewPU;
	rand uvm_reg_field ZCalSlewRateCtrl_p3_ZCalTxSlewPD;
	rand uvm_reg_field ZCalTxSlewPD;
	rand uvm_reg_field TxSeg120_p3_TxSeg120PU0;
	rand uvm_reg_field TxSeg120PU0;
	rand uvm_reg_field TxSeg120_p3_TxSeg120PD0;
	rand uvm_reg_field TxSeg120PD0;
	rand uvm_reg_field TxSeg120_p3_TxSeg120PU1;
	rand uvm_reg_field TxSeg120PU1;
	rand uvm_reg_field TxSeg120_p3_TxSeg120PD1;
	rand uvm_reg_field TxSeg120PD1;
	rand uvm_reg_field RxVrefDac_p3_RxVrefDac_p3;
	rand uvm_reg_field OdtSeg120_p3_OdtSeg120PU0;
	rand uvm_reg_field OdtSeg120PU0;
	rand uvm_reg_field OdtSeg120_p3_OdtSeg120PD0;
	rand uvm_reg_field OdtSeg120PD0;
	rand uvm_reg_field OdtSeg120_p3_OdtSeg120PU1;
	rand uvm_reg_field OdtSeg120PU1;
	rand uvm_reg_field OdtSeg120_p3_OdtSeg120PD1;
	rand uvm_reg_field OdtSeg120PD1;
	rand uvm_reg_field ReservedPZCAL_p3_ReservedPZCAL_p3;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	RxDfeModeCfg_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h9 };
		option.weight = 1;
	}

	HMReservedP1_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFF };
		option.weight = 1;
	}

	ZCalCompCtrl_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h30B };
		option.weight = 1;
	}

	ZCalSlewRateCtrl_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h30C };
		option.weight = 1;
	}

	TxSeg120_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3E0 };
		option.weight = 1;
	}

	RxVrefDac_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3E1 };
		option.weight = 1;
	}

	OdtSeg120_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3FF };
		option.weight = 1;
	}

	ReservedPZCAL_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h501 };
		option.weight = 1;
	}
endgroup
	function new(string name = "DWC_DDRPHYA_HMZCAL0_p3");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.RxDfeModeCfg_p3 = ral_reg_DWC_DDRPHYA_HMZCAL0_p3_RxDfeModeCfg_p3::type_id::create("RxDfeModeCfg_p3",,get_full_name());
      if(this.RxDfeModeCfg_p3.has_coverage(UVM_CVR_ALL))
      	this.RxDfeModeCfg_p3.cg_bits.option.name = {get_name(), ".", "RxDfeModeCfg_p3_bits"};
      this.RxDfeModeCfg_p3.configure(this, null, "");
      this.RxDfeModeCfg_p3.build();
      this.default_map.add_reg(this.RxDfeModeCfg_p3, `UVM_REG_ADDR_WIDTH'h9, "RW", 0);
		this.RxDfeModeCfg_p3_RxDfeCtrl = this.RxDfeModeCfg_p3.RxDfeCtrl;
		this.RxDfeCtrl = this.RxDfeModeCfg_p3.RxDfeCtrl;
      this.HMReservedP1_p3 = ral_reg_DWC_DDRPHYA_HMZCAL0_p3_HMReservedP1_p3::type_id::create("HMReservedP1_p3",,get_full_name());
      if(this.HMReservedP1_p3.has_coverage(UVM_CVR_ALL))
      	this.HMReservedP1_p3.cg_bits.option.name = {get_name(), ".", "HMReservedP1_p3_bits"};
      this.HMReservedP1_p3.configure(this, null, "");
      this.HMReservedP1_p3.build();
      this.default_map.add_reg(this.HMReservedP1_p3, `UVM_REG_ADDR_WIDTH'hFF, "RW", 0);
		this.HMReservedP1_p3_HMReservedP1_p3 = this.HMReservedP1_p3.HMReservedP1_p3;
      this.ZCalCompCtrl_p3 = ral_reg_DWC_DDRPHYA_HMZCAL0_p3_ZCalCompCtrl_p3::type_id::create("ZCalCompCtrl_p3",,get_full_name());
      if(this.ZCalCompCtrl_p3.has_coverage(UVM_CVR_ALL))
      	this.ZCalCompCtrl_p3.cg_bits.option.name = {get_name(), ".", "ZCalCompCtrl_p3_bits"};
      this.ZCalCompCtrl_p3.configure(this, null, "");
      this.ZCalCompCtrl_p3.build();
      this.default_map.add_reg(this.ZCalCompCtrl_p3, `UVM_REG_ADDR_WIDTH'h30B, "RW", 0);
		this.ZCalCompCtrl_p3_ZCalCompGainCurrAdj = this.ZCalCompCtrl_p3.ZCalCompGainCurrAdj;
		this.ZCalCompGainCurrAdj = this.ZCalCompCtrl_p3.ZCalCompGainCurrAdj;
      this.ZCalSlewRateCtrl_p3 = ral_reg_DWC_DDRPHYA_HMZCAL0_p3_ZCalSlewRateCtrl_p3::type_id::create("ZCalSlewRateCtrl_p3",,get_full_name());
      if(this.ZCalSlewRateCtrl_p3.has_coverage(UVM_CVR_ALL))
      	this.ZCalSlewRateCtrl_p3.cg_bits.option.name = {get_name(), ".", "ZCalSlewRateCtrl_p3_bits"};
      this.ZCalSlewRateCtrl_p3.configure(this, null, "");
      this.ZCalSlewRateCtrl_p3.build();
      this.default_map.add_reg(this.ZCalSlewRateCtrl_p3, `UVM_REG_ADDR_WIDTH'h30C, "RW", 0);
		this.ZCalSlewRateCtrl_p3_ZCalTxSlewPU = this.ZCalSlewRateCtrl_p3.ZCalTxSlewPU;
		this.ZCalTxSlewPU = this.ZCalSlewRateCtrl_p3.ZCalTxSlewPU;
		this.ZCalSlewRateCtrl_p3_ZCalTxSlewPD = this.ZCalSlewRateCtrl_p3.ZCalTxSlewPD;
		this.ZCalTxSlewPD = this.ZCalSlewRateCtrl_p3.ZCalTxSlewPD;
      this.TxSeg120_p3 = ral_reg_DWC_DDRPHYA_HMZCAL0_p3_TxSeg120_p3::type_id::create("TxSeg120_p3",,get_full_name());
      if(this.TxSeg120_p3.has_coverage(UVM_CVR_ALL))
      	this.TxSeg120_p3.cg_bits.option.name = {get_name(), ".", "TxSeg120_p3_bits"};
      this.TxSeg120_p3.configure(this, null, "");
      this.TxSeg120_p3.build();
      this.default_map.add_reg(this.TxSeg120_p3, `UVM_REG_ADDR_WIDTH'h3E0, "RW", 0);
		this.TxSeg120_p3_TxSeg120PU0 = this.TxSeg120_p3.TxSeg120PU0;
		this.TxSeg120PU0 = this.TxSeg120_p3.TxSeg120PU0;
		this.TxSeg120_p3_TxSeg120PD0 = this.TxSeg120_p3.TxSeg120PD0;
		this.TxSeg120PD0 = this.TxSeg120_p3.TxSeg120PD0;
		this.TxSeg120_p3_TxSeg120PU1 = this.TxSeg120_p3.TxSeg120PU1;
		this.TxSeg120PU1 = this.TxSeg120_p3.TxSeg120PU1;
		this.TxSeg120_p3_TxSeg120PD1 = this.TxSeg120_p3.TxSeg120PD1;
		this.TxSeg120PD1 = this.TxSeg120_p3.TxSeg120PD1;
      this.RxVrefDac_p3 = ral_reg_DWC_DDRPHYA_HMZCAL0_p3_RxVrefDac_p3::type_id::create("RxVrefDac_p3",,get_full_name());
      if(this.RxVrefDac_p3.has_coverage(UVM_CVR_ALL))
      	this.RxVrefDac_p3.cg_bits.option.name = {get_name(), ".", "RxVrefDac_p3_bits"};
      this.RxVrefDac_p3.configure(this, null, "");
      this.RxVrefDac_p3.build();
      this.default_map.add_reg(this.RxVrefDac_p3, `UVM_REG_ADDR_WIDTH'h3E1, "RW", 0);
		this.RxVrefDac_p3_RxVrefDac_p3 = this.RxVrefDac_p3.RxVrefDac_p3;
      this.OdtSeg120_p3 = ral_reg_DWC_DDRPHYA_HMZCAL0_p3_OdtSeg120_p3::type_id::create("OdtSeg120_p3",,get_full_name());
      if(this.OdtSeg120_p3.has_coverage(UVM_CVR_ALL))
      	this.OdtSeg120_p3.cg_bits.option.name = {get_name(), ".", "OdtSeg120_p3_bits"};
      this.OdtSeg120_p3.configure(this, null, "");
      this.OdtSeg120_p3.build();
      this.default_map.add_reg(this.OdtSeg120_p3, `UVM_REG_ADDR_WIDTH'h3FF, "RW", 0);
		this.OdtSeg120_p3_OdtSeg120PU0 = this.OdtSeg120_p3.OdtSeg120PU0;
		this.OdtSeg120PU0 = this.OdtSeg120_p3.OdtSeg120PU0;
		this.OdtSeg120_p3_OdtSeg120PD0 = this.OdtSeg120_p3.OdtSeg120PD0;
		this.OdtSeg120PD0 = this.OdtSeg120_p3.OdtSeg120PD0;
		this.OdtSeg120_p3_OdtSeg120PU1 = this.OdtSeg120_p3.OdtSeg120PU1;
		this.OdtSeg120PU1 = this.OdtSeg120_p3.OdtSeg120PU1;
		this.OdtSeg120_p3_OdtSeg120PD1 = this.OdtSeg120_p3.OdtSeg120PD1;
		this.OdtSeg120PD1 = this.OdtSeg120_p3.OdtSeg120PD1;
      this.ReservedPZCAL_p3 = ral_reg_DWC_DDRPHYA_HMZCAL0_p3_ReservedPZCAL_p3::type_id::create("ReservedPZCAL_p3",,get_full_name());
      if(this.ReservedPZCAL_p3.has_coverage(UVM_CVR_ALL))
      	this.ReservedPZCAL_p3.cg_bits.option.name = {get_name(), ".", "ReservedPZCAL_p3_bits"};
      this.ReservedPZCAL_p3.configure(this, null, "");
      this.ReservedPZCAL_p3.build();
      this.default_map.add_reg(this.ReservedPZCAL_p3, `UVM_REG_ADDR_WIDTH'h501, "RW", 0);
		this.ReservedPZCAL_p3_ReservedPZCAL_p3 = this.ReservedPZCAL_p3.ReservedPZCAL_p3;
   endfunction : build

	`uvm_object_utils(ral_block_DWC_DDRPHYA_HMZCAL0_p3)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_DDRPHYA_HMZCAL0_p3


endpackage
`endif
