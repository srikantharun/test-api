`ifndef RAL_DWC_DDRPHYA_PPGC0_P3_PKG
`define RAL_DWC_DDRPHYA_PPGC0_P3_PKG

package ral_DWC_DDRPHYA_PPGC0_p3_pkg;
import uvm_pkg::*;

class ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiCustMode_p3 extends uvm_reg;
	rand uvm_reg_field DfiCustMode_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiCustMode_p3: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_DfiCustMode_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiCustMode_p3 = uvm_reg_field::type_id::create("DfiCustMode_p3",,get_full_name());
      this.DfiCustMode_p3.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiCustMode_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiCustMode_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_HwtMRL_p3 extends uvm_reg;
	rand uvm_reg_field HwtMRL_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HwtMRL_p3: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_HwtMRL_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HwtMRL_p3 = uvm_reg_field::type_id::create("HwtMRL_p3",,get_full_name());
      this.HwtMRL_p3.configure(this, 6, 0, "RW", 0, 6'h6, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_HwtMRL_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_HwtMRL_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_PPTTrainSetup_p3 extends uvm_reg;
	rand uvm_reg_field PhyMstrTrainInterval;
	rand uvm_reg_field PhyMstrMaxReqToAck;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PhyMstrTrainInterval: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   PhyMstrMaxReqToAck: coverpoint {m_data[6:4], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_PPTTrainSetup_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PhyMstrTrainInterval = uvm_reg_field::type_id::create("PhyMstrTrainInterval",,get_full_name());
      this.PhyMstrTrainInterval.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.PhyMstrMaxReqToAck = uvm_reg_field::type_id::create("PhyMstrMaxReqToAck",,get_full_name());
      this.PhyMstrMaxReqToAck.configure(this, 3, 4, "RW", 0, 3'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_PPTTrainSetup_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_PPTTrainSetup_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_PhyMstrFreqOverride_p3 extends uvm_reg;
	rand uvm_reg_field PhyMstrFreqOverride_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PhyMstrFreqOverride_p3: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_PhyMstrFreqOverride_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PhyMstrFreqOverride_p3 = uvm_reg_field::type_id::create("PhyMstrFreqOverride_p3",,get_full_name());
      this.PhyMstrFreqOverride_p3.configure(this, 5, 0, "RW", 0, 5'h2, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_PhyMstrFreqOverride_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_PhyMstrFreqOverride_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiHandshakeDelays0_p3 extends uvm_reg;
	rand uvm_reg_field PhyUpdAckDelay0;
	rand uvm_reg_field PhyUpdReqDelay0;
	rand uvm_reg_field CtrlUpdReqDelay0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PhyUpdAckDelay0: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   PhyUpdReqDelay0: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   CtrlUpdReqDelay0: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_DfiHandshakeDelays0_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PhyUpdAckDelay0 = uvm_reg_field::type_id::create("PhyUpdAckDelay0",,get_full_name());
      this.PhyUpdAckDelay0.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.PhyUpdReqDelay0 = uvm_reg_field::type_id::create("PhyUpdReqDelay0",,get_full_name());
      this.PhyUpdReqDelay0.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.CtrlUpdReqDelay0 = uvm_reg_field::type_id::create("CtrlUpdReqDelay0",,get_full_name());
      this.CtrlUpdReqDelay0.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiHandshakeDelays0_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiHandshakeDelays0_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiRespHandshakeDelays0_p3 extends uvm_reg;
	rand uvm_reg_field LpCtrlAckDelay0;
	rand uvm_reg_field LpDataAckDelay0;
	rand uvm_reg_field CtrlUpdAckDelay0;
	rand uvm_reg_field LpAssertAckDelay0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   LpCtrlAckDelay0: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   LpDataAckDelay0: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   CtrlUpdAckDelay0: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   LpAssertAckDelay0: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_DfiRespHandshakeDelays0_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.LpCtrlAckDelay0 = uvm_reg_field::type_id::create("LpCtrlAckDelay0",,get_full_name());
      this.LpCtrlAckDelay0.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.LpDataAckDelay0 = uvm_reg_field::type_id::create("LpDataAckDelay0",,get_full_name());
      this.LpDataAckDelay0.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.CtrlUpdAckDelay0 = uvm_reg_field::type_id::create("CtrlUpdAckDelay0",,get_full_name());
      this.CtrlUpdAckDelay0.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.LpAssertAckDelay0 = uvm_reg_field::type_id::create("LpAssertAckDelay0",,get_full_name());
      this.LpAssertAckDelay0.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiRespHandshakeDelays0_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiRespHandshakeDelays0_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiHandshakeDelays1_p3 extends uvm_reg;
	rand uvm_reg_field PhyUpdAckDelay1;
	rand uvm_reg_field PhyUpdReqDelay1;
	rand uvm_reg_field CtrlUpdReqDelay1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PhyUpdAckDelay1: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   PhyUpdReqDelay1: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   CtrlUpdReqDelay1: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_DfiHandshakeDelays1_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PhyUpdAckDelay1 = uvm_reg_field::type_id::create("PhyUpdAckDelay1",,get_full_name());
      this.PhyUpdAckDelay1.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.PhyUpdReqDelay1 = uvm_reg_field::type_id::create("PhyUpdReqDelay1",,get_full_name());
      this.PhyUpdReqDelay1.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.CtrlUpdReqDelay1 = uvm_reg_field::type_id::create("CtrlUpdReqDelay1",,get_full_name());
      this.CtrlUpdReqDelay1.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiHandshakeDelays1_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiHandshakeDelays1_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiRespHandshakeDelays1_p3 extends uvm_reg;
	rand uvm_reg_field LpCtrlAckDelay1;
	rand uvm_reg_field LpDataAckDelay1;
	rand uvm_reg_field CtrlUpdAckDelay1;
	rand uvm_reg_field LpAssertAckDelay1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   LpCtrlAckDelay1: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   LpDataAckDelay1: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   CtrlUpdAckDelay1: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   LpAssertAckDelay1: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_DfiRespHandshakeDelays1_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.LpCtrlAckDelay1 = uvm_reg_field::type_id::create("LpCtrlAckDelay1",,get_full_name());
      this.LpCtrlAckDelay1.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.LpDataAckDelay1 = uvm_reg_field::type_id::create("LpDataAckDelay1",,get_full_name());
      this.LpDataAckDelay1.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.CtrlUpdAckDelay1 = uvm_reg_field::type_id::create("CtrlUpdAckDelay1",,get_full_name());
      this.CtrlUpdAckDelay1.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.LpAssertAckDelay1 = uvm_reg_field::type_id::create("LpAssertAckDelay1",,get_full_name());
      this.LpAssertAckDelay1.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiRespHandshakeDelays1_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiRespHandshakeDelays1_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_PUBReservedP1_p3 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_PUBReservedP1_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PUBReservedP1_p3 = uvm_reg_field::type_id::create("PUBReservedP1_p3",,get_full_name());
      this.PUBReservedP1_p3.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_PUBReservedP1_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_PUBReservedP1_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMStartAddr_p3 extends uvm_reg;
	rand uvm_reg_field ACSMStartAddr_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMStartAddr_p3: coverpoint {m_data[10:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMStartAddr_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMStartAddr_p3 = uvm_reg_field::type_id::create("ACSMStartAddr_p3",,get_full_name());
      this.ACSMStartAddr_p3.configure(this, 11, 0, "RW", 0, 11'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMStartAddr_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMStartAddr_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMStopAddr_p3 extends uvm_reg;
	rand uvm_reg_field ACSMStopAddr_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMStopAddr_p3: coverpoint {m_data[10:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMStopAddr_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMStopAddr_p3 = uvm_reg_field::type_id::create("ACSMStopAddr_p3",,get_full_name());
      this.ACSMStopAddr_p3.configure(this, 11, 0, "RW", 0, 11'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMStopAddr_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMStopAddr_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRxEnPulse_p3 extends uvm_reg;
	rand uvm_reg_field ACSMRxEnDelay;
	rand uvm_reg_field ACSMRxEnDelayReserved;
	rand uvm_reg_field ACSMRxEnWidth;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMRxEnDelay: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   ACSMRxEnDelayReserved: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ACSMRxEnWidth: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMRxEnPulse_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMRxEnDelay = uvm_reg_field::type_id::create("ACSMRxEnDelay",,get_full_name());
      this.ACSMRxEnDelay.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 0);
      this.ACSMRxEnDelayReserved = uvm_reg_field::type_id::create("ACSMRxEnDelayReserved",,get_full_name());
      this.ACSMRxEnDelayReserved.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ACSMRxEnWidth = uvm_reg_field::type_id::create("ACSMRxEnWidth",,get_full_name());
      this.ACSMRxEnWidth.configure(this, 6, 8, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRxEnPulse_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRxEnPulse_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRxValPulse_p3 extends uvm_reg;
	rand uvm_reg_field ACSMRxValDelay;
	rand uvm_reg_field ACSMRxValDelayReserved;
	rand uvm_reg_field ACSMRxValWidth;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMRxValDelay: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   ACSMRxValDelayReserved: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ACSMRxValWidth: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMRxValPulse_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMRxValDelay = uvm_reg_field::type_id::create("ACSMRxValDelay",,get_full_name());
      this.ACSMRxValDelay.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 0);
      this.ACSMRxValDelayReserved = uvm_reg_field::type_id::create("ACSMRxValDelayReserved",,get_full_name());
      this.ACSMRxValDelayReserved.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ACSMRxValWidth = uvm_reg_field::type_id::create("ACSMRxValWidth",,get_full_name());
      this.ACSMRxValWidth.configure(this, 6, 8, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRxValPulse_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRxValPulse_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMTxEnPulse_p3 extends uvm_reg;
	rand uvm_reg_field ACSMTxEnDelay;
	rand uvm_reg_field ACSMTxEnDelayReserved;
	rand uvm_reg_field ACSMTxEnWidth;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMTxEnDelay: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   ACSMTxEnDelayReserved: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ACSMTxEnWidth: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMTxEnPulse_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMTxEnDelay = uvm_reg_field::type_id::create("ACSMTxEnDelay",,get_full_name());
      this.ACSMTxEnDelay.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 0);
      this.ACSMTxEnDelayReserved = uvm_reg_field::type_id::create("ACSMTxEnDelayReserved",,get_full_name());
      this.ACSMTxEnDelayReserved.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ACSMTxEnWidth = uvm_reg_field::type_id::create("ACSMTxEnWidth",,get_full_name());
      this.ACSMTxEnWidth.configure(this, 6, 8, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMTxEnPulse_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMTxEnPulse_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWrcsPulse_p3 extends uvm_reg;
	rand uvm_reg_field ACSMWrcsDelay;
	rand uvm_reg_field ACSMWrcsDelayReserved;
	rand uvm_reg_field ACSMWrcsWidth;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMWrcsDelay: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   ACSMWrcsDelayReserved: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ACSMWrcsWidth: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMWrcsPulse_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMWrcsDelay = uvm_reg_field::type_id::create("ACSMWrcsDelay",,get_full_name());
      this.ACSMWrcsDelay.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 0);
      this.ACSMWrcsDelayReserved = uvm_reg_field::type_id::create("ACSMWrcsDelayReserved",,get_full_name());
      this.ACSMWrcsDelayReserved.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ACSMWrcsWidth = uvm_reg_field::type_id::create("ACSMWrcsWidth",,get_full_name());
      this.ACSMWrcsWidth.configure(this, 6, 8, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWrcsPulse_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWrcsPulse_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRdcsPulse_p3 extends uvm_reg;
	rand uvm_reg_field ACSMRdcsDelay;
	rand uvm_reg_field ACSMRdcsDelayReserved;
	rand uvm_reg_field ACSMRdcsWidth;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMRdcsDelay: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   ACSMRdcsDelayReserved: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ACSMRdcsWidth: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMRdcsPulse_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMRdcsDelay = uvm_reg_field::type_id::create("ACSMRdcsDelay",,get_full_name());
      this.ACSMRdcsDelay.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 0);
      this.ACSMRdcsDelayReserved = uvm_reg_field::type_id::create("ACSMRdcsDelayReserved",,get_full_name());
      this.ACSMRdcsDelayReserved.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ACSMRdcsWidth = uvm_reg_field::type_id::create("ACSMRdcsWidth",,get_full_name());
      this.ACSMRdcsWidth.configure(this, 6, 8, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRdcsPulse_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRdcsPulse_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteStaticLoPulse_p3 extends uvm_reg;
	rand uvm_reg_field ACSMWckWriteStaticLoDelay;
	rand uvm_reg_field ACSMWckWriteStaticLoDelayReserved;
	rand uvm_reg_field ACSMWckWriteStaticLoWidth;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMWckWriteStaticLoDelay: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   ACSMWckWriteStaticLoDelayReserved: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ACSMWckWriteStaticLoWidth: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteStaticLoPulse_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMWckWriteStaticLoDelay = uvm_reg_field::type_id::create("ACSMWckWriteStaticLoDelay",,get_full_name());
      this.ACSMWckWriteStaticLoDelay.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 0);
      this.ACSMWckWriteStaticLoDelayReserved = uvm_reg_field::type_id::create("ACSMWckWriteStaticLoDelayReserved",,get_full_name());
      this.ACSMWckWriteStaticLoDelayReserved.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ACSMWckWriteStaticLoWidth = uvm_reg_field::type_id::create("ACSMWckWriteStaticLoWidth",,get_full_name());
      this.ACSMWckWriteStaticLoWidth.configure(this, 6, 8, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteStaticLoPulse_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteStaticLoPulse_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteStaticHiPulse_p3 extends uvm_reg;
	rand uvm_reg_field ACSMWckWriteStaticHiDelay;
	rand uvm_reg_field ACSMWckWriteStaticHiDelayReserved;
	rand uvm_reg_field ACSMWckWriteStaticHiWidth;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMWckWriteStaticHiDelay: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   ACSMWckWriteStaticHiDelayReserved: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ACSMWckWriteStaticHiWidth: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteStaticHiPulse_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMWckWriteStaticHiDelay = uvm_reg_field::type_id::create("ACSMWckWriteStaticHiDelay",,get_full_name());
      this.ACSMWckWriteStaticHiDelay.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 0);
      this.ACSMWckWriteStaticHiDelayReserved = uvm_reg_field::type_id::create("ACSMWckWriteStaticHiDelayReserved",,get_full_name());
      this.ACSMWckWriteStaticHiDelayReserved.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ACSMWckWriteStaticHiWidth = uvm_reg_field::type_id::create("ACSMWckWriteStaticHiWidth",,get_full_name());
      this.ACSMWckWriteStaticHiWidth.configure(this, 6, 8, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteStaticHiPulse_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteStaticHiPulse_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteTogglePulse_p3 extends uvm_reg;
	rand uvm_reg_field ACSMWckWriteToggleDelay;
	rand uvm_reg_field ACSMWckWriteToggleDelayReserved;
	rand uvm_reg_field ACSMWckWriteToggleWidth;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMWckWriteToggleDelay: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   ACSMWckWriteToggleDelayReserved: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ACSMWckWriteToggleWidth: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteTogglePulse_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMWckWriteToggleDelay = uvm_reg_field::type_id::create("ACSMWckWriteToggleDelay",,get_full_name());
      this.ACSMWckWriteToggleDelay.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 0);
      this.ACSMWckWriteToggleDelayReserved = uvm_reg_field::type_id::create("ACSMWckWriteToggleDelayReserved",,get_full_name());
      this.ACSMWckWriteToggleDelayReserved.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ACSMWckWriteToggleWidth = uvm_reg_field::type_id::create("ACSMWckWriteToggleWidth",,get_full_name());
      this.ACSMWckWriteToggleWidth.configure(this, 6, 8, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteTogglePulse_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteTogglePulse_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteFastTogglePulse_p3 extends uvm_reg;
	rand uvm_reg_field ACSMWckWriteFastToggleDelay;
	rand uvm_reg_field ACSMWckWriteFastToggleDelayReserved;
	rand uvm_reg_field ACSMWckWriteFastToggleWidth;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMWckWriteFastToggleDelay: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   ACSMWckWriteFastToggleDelayReserved: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ACSMWckWriteFastToggleWidth: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteFastTogglePulse_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMWckWriteFastToggleDelay = uvm_reg_field::type_id::create("ACSMWckWriteFastToggleDelay",,get_full_name());
      this.ACSMWckWriteFastToggleDelay.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 0);
      this.ACSMWckWriteFastToggleDelayReserved = uvm_reg_field::type_id::create("ACSMWckWriteFastToggleDelayReserved",,get_full_name());
      this.ACSMWckWriteFastToggleDelayReserved.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ACSMWckWriteFastToggleWidth = uvm_reg_field::type_id::create("ACSMWckWriteFastToggleWidth",,get_full_name());
      this.ACSMWckWriteFastToggleWidth.configure(this, 6, 8, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteFastTogglePulse_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteFastTogglePulse_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckReadStaticLoPulse_p3 extends uvm_reg;
	rand uvm_reg_field ACSMWckReadStaticLoDelay;
	rand uvm_reg_field ACSMWckReadStaticLoDelayReserved;
	rand uvm_reg_field ACSMWckReadStaticLoWidth;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMWckReadStaticLoDelay: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   ACSMWckReadStaticLoDelayReserved: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ACSMWckReadStaticLoWidth: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMWckReadStaticLoPulse_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMWckReadStaticLoDelay = uvm_reg_field::type_id::create("ACSMWckReadStaticLoDelay",,get_full_name());
      this.ACSMWckReadStaticLoDelay.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 0);
      this.ACSMWckReadStaticLoDelayReserved = uvm_reg_field::type_id::create("ACSMWckReadStaticLoDelayReserved",,get_full_name());
      this.ACSMWckReadStaticLoDelayReserved.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ACSMWckReadStaticLoWidth = uvm_reg_field::type_id::create("ACSMWckReadStaticLoWidth",,get_full_name());
      this.ACSMWckReadStaticLoWidth.configure(this, 6, 8, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckReadStaticLoPulse_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckReadStaticLoPulse_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckReadStaticHiPulse_p3 extends uvm_reg;
	rand uvm_reg_field ACSMWckReadStaticHiDelay;
	rand uvm_reg_field ACSMWckReadStaticHiDelayReserved;
	rand uvm_reg_field ACSMWckReadStaticHiWidth;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMWckReadStaticHiDelay: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   ACSMWckReadStaticHiDelayReserved: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ACSMWckReadStaticHiWidth: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMWckReadStaticHiPulse_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMWckReadStaticHiDelay = uvm_reg_field::type_id::create("ACSMWckReadStaticHiDelay",,get_full_name());
      this.ACSMWckReadStaticHiDelay.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 0);
      this.ACSMWckReadStaticHiDelayReserved = uvm_reg_field::type_id::create("ACSMWckReadStaticHiDelayReserved",,get_full_name());
      this.ACSMWckReadStaticHiDelayReserved.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ACSMWckReadStaticHiWidth = uvm_reg_field::type_id::create("ACSMWckReadStaticHiWidth",,get_full_name());
      this.ACSMWckReadStaticHiWidth.configure(this, 6, 8, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckReadStaticHiPulse_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckReadStaticHiPulse_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckReadTogglePulse_p3 extends uvm_reg;
	rand uvm_reg_field ACSMWckReadToggleDelay;
	rand uvm_reg_field ACSMWckReadToggleDelayReserved;
	rand uvm_reg_field ACSMWckReadToggleWidth;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMWckReadToggleDelay: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   ACSMWckReadToggleDelayReserved: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ACSMWckReadToggleWidth: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMWckReadTogglePulse_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMWckReadToggleDelay = uvm_reg_field::type_id::create("ACSMWckReadToggleDelay",,get_full_name());
      this.ACSMWckReadToggleDelay.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 0);
      this.ACSMWckReadToggleDelayReserved = uvm_reg_field::type_id::create("ACSMWckReadToggleDelayReserved",,get_full_name());
      this.ACSMWckReadToggleDelayReserved.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ACSMWckReadToggleWidth = uvm_reg_field::type_id::create("ACSMWckReadToggleWidth",,get_full_name());
      this.ACSMWckReadToggleWidth.configure(this, 6, 8, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckReadTogglePulse_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckReadTogglePulse_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckReadFastTogglePulse_p3 extends uvm_reg;
	rand uvm_reg_field ACSMWckReadFastToggleDelay;
	rand uvm_reg_field ACSMWckReadFastToggleDelayReserved;
	rand uvm_reg_field ACSMWckReadFastToggleWidth;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMWckReadFastToggleDelay: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   ACSMWckReadFastToggleDelayReserved: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ACSMWckReadFastToggleWidth: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMWckReadFastTogglePulse_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMWckReadFastToggleDelay = uvm_reg_field::type_id::create("ACSMWckReadFastToggleDelay",,get_full_name());
      this.ACSMWckReadFastToggleDelay.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 0);
      this.ACSMWckReadFastToggleDelayReserved = uvm_reg_field::type_id::create("ACSMWckReadFastToggleDelayReserved",,get_full_name());
      this.ACSMWckReadFastToggleDelayReserved.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ACSMWckReadFastToggleWidth = uvm_reg_field::type_id::create("ACSMWckReadFastToggleWidth",,get_full_name());
      this.ACSMWckReadFastToggleWidth.configure(this, 6, 8, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckReadFastTogglePulse_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckReadFastTogglePulse_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwStaticLoPulse_p3 extends uvm_reg;
	rand uvm_reg_field ACSMWckFreqSwStaticLoDelay;
	rand uvm_reg_field ACSMWckFreqSwStaticLoDelayReserved;
	rand uvm_reg_field ACSMWckFreqSwStaticLoWidth;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMWckFreqSwStaticLoDelay: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   ACSMWckFreqSwStaticLoDelayReserved: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ACSMWckFreqSwStaticLoWidth: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwStaticLoPulse_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMWckFreqSwStaticLoDelay = uvm_reg_field::type_id::create("ACSMWckFreqSwStaticLoDelay",,get_full_name());
      this.ACSMWckFreqSwStaticLoDelay.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 0);
      this.ACSMWckFreqSwStaticLoDelayReserved = uvm_reg_field::type_id::create("ACSMWckFreqSwStaticLoDelayReserved",,get_full_name());
      this.ACSMWckFreqSwStaticLoDelayReserved.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ACSMWckFreqSwStaticLoWidth = uvm_reg_field::type_id::create("ACSMWckFreqSwStaticLoWidth",,get_full_name());
      this.ACSMWckFreqSwStaticLoWidth.configure(this, 6, 8, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwStaticLoPulse_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwStaticLoPulse_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwStaticHiPulse_p3 extends uvm_reg;
	rand uvm_reg_field ACSMWckFreqSwStaticHiDelay;
	rand uvm_reg_field ACSMWckFreqSwStaticHiDelayReserved;
	rand uvm_reg_field ACSMWckFreqSwStaticHiWidth;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMWckFreqSwStaticHiDelay: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   ACSMWckFreqSwStaticHiDelayReserved: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ACSMWckFreqSwStaticHiWidth: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwStaticHiPulse_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMWckFreqSwStaticHiDelay = uvm_reg_field::type_id::create("ACSMWckFreqSwStaticHiDelay",,get_full_name());
      this.ACSMWckFreqSwStaticHiDelay.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 0);
      this.ACSMWckFreqSwStaticHiDelayReserved = uvm_reg_field::type_id::create("ACSMWckFreqSwStaticHiDelayReserved",,get_full_name());
      this.ACSMWckFreqSwStaticHiDelayReserved.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ACSMWckFreqSwStaticHiWidth = uvm_reg_field::type_id::create("ACSMWckFreqSwStaticHiWidth",,get_full_name());
      this.ACSMWckFreqSwStaticHiWidth.configure(this, 6, 8, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwStaticHiPulse_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwStaticHiPulse_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwTogglePulse_p3 extends uvm_reg;
	rand uvm_reg_field ACSMWckFreqSwToggleDelay;
	rand uvm_reg_field ACSMWckFreqSwToggleDelayReserved;
	rand uvm_reg_field ACSMWckFreqSwToggleWidth;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMWckFreqSwToggleDelay: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   ACSMWckFreqSwToggleDelayReserved: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ACSMWckFreqSwToggleWidth: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwTogglePulse_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMWckFreqSwToggleDelay = uvm_reg_field::type_id::create("ACSMWckFreqSwToggleDelay",,get_full_name());
      this.ACSMWckFreqSwToggleDelay.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 0);
      this.ACSMWckFreqSwToggleDelayReserved = uvm_reg_field::type_id::create("ACSMWckFreqSwToggleDelayReserved",,get_full_name());
      this.ACSMWckFreqSwToggleDelayReserved.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ACSMWckFreqSwToggleWidth = uvm_reg_field::type_id::create("ACSMWckFreqSwToggleWidth",,get_full_name());
      this.ACSMWckFreqSwToggleWidth.configure(this, 6, 8, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwTogglePulse_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwTogglePulse_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwFastTogglePulse_p3 extends uvm_reg;
	rand uvm_reg_field ACSMWckFreqSwFastToggleDelay;
	rand uvm_reg_field ACSMWckFreqSwFastToggleDelayReserved;
	rand uvm_reg_field ACSMWckFreqSwFastToggleWidth;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMWckFreqSwFastToggleDelay: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   ACSMWckFreqSwFastToggleDelayReserved: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ACSMWckFreqSwFastToggleWidth: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwFastTogglePulse_p3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMWckFreqSwFastToggleDelay = uvm_reg_field::type_id::create("ACSMWckFreqSwFastToggleDelay",,get_full_name());
      this.ACSMWckFreqSwFastToggleDelay.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 0);
      this.ACSMWckFreqSwFastToggleDelayReserved = uvm_reg_field::type_id::create("ACSMWckFreqSwFastToggleDelayReserved",,get_full_name());
      this.ACSMWckFreqSwFastToggleDelayReserved.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ACSMWckFreqSwFastToggleWidth = uvm_reg_field::type_id::create("ACSMWckFreqSwFastToggleWidth",,get_full_name());
      this.ACSMWckFreqSwFastToggleWidth.configure(this, 6, 8, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwFastTogglePulse_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwFastTogglePulse_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreeRunMode_p3 extends uvm_reg;
	rand uvm_reg_field ACSMWckFreeRunMode_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMWckFreeRunMode_p3: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMWckFreeRunMode_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMWckFreeRunMode_p3 = uvm_reg_field::type_id::create("ACSMWckFreeRunMode_p3",,get_full_name());
      this.ACSMWckFreeRunMode_p3.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreeRunMode_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreeRunMode_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRptCntOverride_p3 extends uvm_reg;
	rand uvm_reg_field ACSMRptCntOverride_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMRptCntOverride_p3: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMRptCntOverride_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMRptCntOverride_p3 = uvm_reg_field::type_id::create("ACSMRptCntOverride_p3",,get_full_name());
      this.ACSMRptCntOverride_p3.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRptCntOverride_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRptCntOverride_p3


class ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRptCntDbl_p3 extends uvm_reg;
	rand uvm_reg_field ACSMRptCntDbl_p3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMRptCntDbl_p3: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_PPGC0_p3_ACSMRptCntDbl_p3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMRptCntDbl_p3 = uvm_reg_field::type_id::create("ACSMRptCntDbl_p3",,get_full_name());
      this.ACSMRptCntDbl_p3.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRptCntDbl_p3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRptCntDbl_p3


class ral_block_DWC_DDRPHYA_PPGC0_p3 extends uvm_reg_block;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiCustMode_p3 DfiCustMode_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_HwtMRL_p3 HwtMRL_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_PPTTrainSetup_p3 PPTTrainSetup_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_PhyMstrFreqOverride_p3 PhyMstrFreqOverride_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiHandshakeDelays0_p3 DfiHandshakeDelays0_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiRespHandshakeDelays0_p3 DfiRespHandshakeDelays0_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiHandshakeDelays1_p3 DfiHandshakeDelays1_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiRespHandshakeDelays1_p3 DfiRespHandshakeDelays1_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_PUBReservedP1_p3 PUBReservedP1_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMStartAddr_p3 ACSMStartAddr_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMStopAddr_p3 ACSMStopAddr_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRxEnPulse_p3 ACSMRxEnPulse_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRxValPulse_p3 ACSMRxValPulse_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMTxEnPulse_p3 ACSMTxEnPulse_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWrcsPulse_p3 ACSMWrcsPulse_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRdcsPulse_p3 ACSMRdcsPulse_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteStaticLoPulse_p3 ACSMWckWriteStaticLoPulse_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteStaticHiPulse_p3 ACSMWckWriteStaticHiPulse_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteTogglePulse_p3 ACSMWckWriteTogglePulse_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteFastTogglePulse_p3 ACSMWckWriteFastTogglePulse_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckReadStaticLoPulse_p3 ACSMWckReadStaticLoPulse_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckReadStaticHiPulse_p3 ACSMWckReadStaticHiPulse_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckReadTogglePulse_p3 ACSMWckReadTogglePulse_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckReadFastTogglePulse_p3 ACSMWckReadFastTogglePulse_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwStaticLoPulse_p3 ACSMWckFreqSwStaticLoPulse_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwStaticHiPulse_p3 ACSMWckFreqSwStaticHiPulse_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwTogglePulse_p3 ACSMWckFreqSwTogglePulse_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwFastTogglePulse_p3 ACSMWckFreqSwFastTogglePulse_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreeRunMode_p3 ACSMWckFreeRunMode_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRptCntOverride_p3 ACSMRptCntOverride_p3;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRptCntDbl_p3 ACSMRptCntDbl_p3;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field DfiCustMode_p3_DfiCustMode_p3;
	rand uvm_reg_field HwtMRL_p3_HwtMRL_p3;
	rand uvm_reg_field PPTTrainSetup_p3_PhyMstrTrainInterval;
	rand uvm_reg_field PhyMstrTrainInterval;
	rand uvm_reg_field PPTTrainSetup_p3_PhyMstrMaxReqToAck;
	rand uvm_reg_field PhyMstrMaxReqToAck;
	rand uvm_reg_field PhyMstrFreqOverride_p3_PhyMstrFreqOverride_p3;
	rand uvm_reg_field DfiHandshakeDelays0_p3_PhyUpdAckDelay0;
	rand uvm_reg_field PhyUpdAckDelay0;
	rand uvm_reg_field DfiHandshakeDelays0_p3_PhyUpdReqDelay0;
	rand uvm_reg_field PhyUpdReqDelay0;
	rand uvm_reg_field DfiHandshakeDelays0_p3_CtrlUpdReqDelay0;
	rand uvm_reg_field CtrlUpdReqDelay0;
	rand uvm_reg_field DfiRespHandshakeDelays0_p3_LpCtrlAckDelay0;
	rand uvm_reg_field LpCtrlAckDelay0;
	rand uvm_reg_field DfiRespHandshakeDelays0_p3_LpDataAckDelay0;
	rand uvm_reg_field LpDataAckDelay0;
	rand uvm_reg_field DfiRespHandshakeDelays0_p3_CtrlUpdAckDelay0;
	rand uvm_reg_field CtrlUpdAckDelay0;
	rand uvm_reg_field DfiRespHandshakeDelays0_p3_LpAssertAckDelay0;
	rand uvm_reg_field LpAssertAckDelay0;
	rand uvm_reg_field DfiHandshakeDelays1_p3_PhyUpdAckDelay1;
	rand uvm_reg_field PhyUpdAckDelay1;
	rand uvm_reg_field DfiHandshakeDelays1_p3_PhyUpdReqDelay1;
	rand uvm_reg_field PhyUpdReqDelay1;
	rand uvm_reg_field DfiHandshakeDelays1_p3_CtrlUpdReqDelay1;
	rand uvm_reg_field CtrlUpdReqDelay1;
	rand uvm_reg_field DfiRespHandshakeDelays1_p3_LpCtrlAckDelay1;
	rand uvm_reg_field LpCtrlAckDelay1;
	rand uvm_reg_field DfiRespHandshakeDelays1_p3_LpDataAckDelay1;
	rand uvm_reg_field LpDataAckDelay1;
	rand uvm_reg_field DfiRespHandshakeDelays1_p3_CtrlUpdAckDelay1;
	rand uvm_reg_field CtrlUpdAckDelay1;
	rand uvm_reg_field DfiRespHandshakeDelays1_p3_LpAssertAckDelay1;
	rand uvm_reg_field LpAssertAckDelay1;
	rand uvm_reg_field PUBReservedP1_p3_PUBReservedP1_p3;
	rand uvm_reg_field ACSMStartAddr_p3_ACSMStartAddr_p3;
	rand uvm_reg_field ACSMStopAddr_p3_ACSMStopAddr_p3;
	rand uvm_reg_field ACSMRxEnPulse_p3_ACSMRxEnDelay;
	rand uvm_reg_field ACSMRxEnDelay;
	rand uvm_reg_field ACSMRxEnPulse_p3_ACSMRxEnDelayReserved;
	rand uvm_reg_field ACSMRxEnDelayReserved;
	rand uvm_reg_field ACSMRxEnPulse_p3_ACSMRxEnWidth;
	rand uvm_reg_field ACSMRxEnWidth;
	rand uvm_reg_field ACSMRxValPulse_p3_ACSMRxValDelay;
	rand uvm_reg_field ACSMRxValDelay;
	rand uvm_reg_field ACSMRxValPulse_p3_ACSMRxValDelayReserved;
	rand uvm_reg_field ACSMRxValDelayReserved;
	rand uvm_reg_field ACSMRxValPulse_p3_ACSMRxValWidth;
	rand uvm_reg_field ACSMRxValWidth;
	rand uvm_reg_field ACSMTxEnPulse_p3_ACSMTxEnDelay;
	rand uvm_reg_field ACSMTxEnDelay;
	rand uvm_reg_field ACSMTxEnPulse_p3_ACSMTxEnDelayReserved;
	rand uvm_reg_field ACSMTxEnDelayReserved;
	rand uvm_reg_field ACSMTxEnPulse_p3_ACSMTxEnWidth;
	rand uvm_reg_field ACSMTxEnWidth;
	rand uvm_reg_field ACSMWrcsPulse_p3_ACSMWrcsDelay;
	rand uvm_reg_field ACSMWrcsDelay;
	rand uvm_reg_field ACSMWrcsPulse_p3_ACSMWrcsDelayReserved;
	rand uvm_reg_field ACSMWrcsDelayReserved;
	rand uvm_reg_field ACSMWrcsPulse_p3_ACSMWrcsWidth;
	rand uvm_reg_field ACSMWrcsWidth;
	rand uvm_reg_field ACSMRdcsPulse_p3_ACSMRdcsDelay;
	rand uvm_reg_field ACSMRdcsDelay;
	rand uvm_reg_field ACSMRdcsPulse_p3_ACSMRdcsDelayReserved;
	rand uvm_reg_field ACSMRdcsDelayReserved;
	rand uvm_reg_field ACSMRdcsPulse_p3_ACSMRdcsWidth;
	rand uvm_reg_field ACSMRdcsWidth;
	rand uvm_reg_field ACSMWckWriteStaticLoPulse_p3_ACSMWckWriteStaticLoDelay;
	rand uvm_reg_field ACSMWckWriteStaticLoDelay;
	rand uvm_reg_field ACSMWckWriteStaticLoPulse_p3_ACSMWckWriteStaticLoDelayReserved;
	rand uvm_reg_field ACSMWckWriteStaticLoDelayReserved;
	rand uvm_reg_field ACSMWckWriteStaticLoPulse_p3_ACSMWckWriteStaticLoWidth;
	rand uvm_reg_field ACSMWckWriteStaticLoWidth;
	rand uvm_reg_field ACSMWckWriteStaticHiPulse_p3_ACSMWckWriteStaticHiDelay;
	rand uvm_reg_field ACSMWckWriteStaticHiDelay;
	rand uvm_reg_field ACSMWckWriteStaticHiPulse_p3_ACSMWckWriteStaticHiDelayReserved;
	rand uvm_reg_field ACSMWckWriteStaticHiDelayReserved;
	rand uvm_reg_field ACSMWckWriteStaticHiPulse_p3_ACSMWckWriteStaticHiWidth;
	rand uvm_reg_field ACSMWckWriteStaticHiWidth;
	rand uvm_reg_field ACSMWckWriteTogglePulse_p3_ACSMWckWriteToggleDelay;
	rand uvm_reg_field ACSMWckWriteToggleDelay;
	rand uvm_reg_field ACSMWckWriteTogglePulse_p3_ACSMWckWriteToggleDelayReserved;
	rand uvm_reg_field ACSMWckWriteToggleDelayReserved;
	rand uvm_reg_field ACSMWckWriteTogglePulse_p3_ACSMWckWriteToggleWidth;
	rand uvm_reg_field ACSMWckWriteToggleWidth;
	rand uvm_reg_field ACSMWckWriteFastTogglePulse_p3_ACSMWckWriteFastToggleDelay;
	rand uvm_reg_field ACSMWckWriteFastToggleDelay;
	rand uvm_reg_field ACSMWckWriteFastTogglePulse_p3_ACSMWckWriteFastToggleDelayReserved;
	rand uvm_reg_field ACSMWckWriteFastToggleDelayReserved;
	rand uvm_reg_field ACSMWckWriteFastTogglePulse_p3_ACSMWckWriteFastToggleWidth;
	rand uvm_reg_field ACSMWckWriteFastToggleWidth;
	rand uvm_reg_field ACSMWckReadStaticLoPulse_p3_ACSMWckReadStaticLoDelay;
	rand uvm_reg_field ACSMWckReadStaticLoDelay;
	rand uvm_reg_field ACSMWckReadStaticLoPulse_p3_ACSMWckReadStaticLoDelayReserved;
	rand uvm_reg_field ACSMWckReadStaticLoDelayReserved;
	rand uvm_reg_field ACSMWckReadStaticLoPulse_p3_ACSMWckReadStaticLoWidth;
	rand uvm_reg_field ACSMWckReadStaticLoWidth;
	rand uvm_reg_field ACSMWckReadStaticHiPulse_p3_ACSMWckReadStaticHiDelay;
	rand uvm_reg_field ACSMWckReadStaticHiDelay;
	rand uvm_reg_field ACSMWckReadStaticHiPulse_p3_ACSMWckReadStaticHiDelayReserved;
	rand uvm_reg_field ACSMWckReadStaticHiDelayReserved;
	rand uvm_reg_field ACSMWckReadStaticHiPulse_p3_ACSMWckReadStaticHiWidth;
	rand uvm_reg_field ACSMWckReadStaticHiWidth;
	rand uvm_reg_field ACSMWckReadTogglePulse_p3_ACSMWckReadToggleDelay;
	rand uvm_reg_field ACSMWckReadToggleDelay;
	rand uvm_reg_field ACSMWckReadTogglePulse_p3_ACSMWckReadToggleDelayReserved;
	rand uvm_reg_field ACSMWckReadToggleDelayReserved;
	rand uvm_reg_field ACSMWckReadTogglePulse_p3_ACSMWckReadToggleWidth;
	rand uvm_reg_field ACSMWckReadToggleWidth;
	rand uvm_reg_field ACSMWckReadFastTogglePulse_p3_ACSMWckReadFastToggleDelay;
	rand uvm_reg_field ACSMWckReadFastToggleDelay;
	rand uvm_reg_field ACSMWckReadFastTogglePulse_p3_ACSMWckReadFastToggleDelayReserved;
	rand uvm_reg_field ACSMWckReadFastToggleDelayReserved;
	rand uvm_reg_field ACSMWckReadFastTogglePulse_p3_ACSMWckReadFastToggleWidth;
	rand uvm_reg_field ACSMWckReadFastToggleWidth;
	rand uvm_reg_field ACSMWckFreqSwStaticLoPulse_p3_ACSMWckFreqSwStaticLoDelay;
	rand uvm_reg_field ACSMWckFreqSwStaticLoDelay;
	rand uvm_reg_field ACSMWckFreqSwStaticLoPulse_p3_ACSMWckFreqSwStaticLoDelayReserved;
	rand uvm_reg_field ACSMWckFreqSwStaticLoDelayReserved;
	rand uvm_reg_field ACSMWckFreqSwStaticLoPulse_p3_ACSMWckFreqSwStaticLoWidth;
	rand uvm_reg_field ACSMWckFreqSwStaticLoWidth;
	rand uvm_reg_field ACSMWckFreqSwStaticHiPulse_p3_ACSMWckFreqSwStaticHiDelay;
	rand uvm_reg_field ACSMWckFreqSwStaticHiDelay;
	rand uvm_reg_field ACSMWckFreqSwStaticHiPulse_p3_ACSMWckFreqSwStaticHiDelayReserved;
	rand uvm_reg_field ACSMWckFreqSwStaticHiDelayReserved;
	rand uvm_reg_field ACSMWckFreqSwStaticHiPulse_p3_ACSMWckFreqSwStaticHiWidth;
	rand uvm_reg_field ACSMWckFreqSwStaticHiWidth;
	rand uvm_reg_field ACSMWckFreqSwTogglePulse_p3_ACSMWckFreqSwToggleDelay;
	rand uvm_reg_field ACSMWckFreqSwToggleDelay;
	rand uvm_reg_field ACSMWckFreqSwTogglePulse_p3_ACSMWckFreqSwToggleDelayReserved;
	rand uvm_reg_field ACSMWckFreqSwToggleDelayReserved;
	rand uvm_reg_field ACSMWckFreqSwTogglePulse_p3_ACSMWckFreqSwToggleWidth;
	rand uvm_reg_field ACSMWckFreqSwToggleWidth;
	rand uvm_reg_field ACSMWckFreqSwFastTogglePulse_p3_ACSMWckFreqSwFastToggleDelay;
	rand uvm_reg_field ACSMWckFreqSwFastToggleDelay;
	rand uvm_reg_field ACSMWckFreqSwFastTogglePulse_p3_ACSMWckFreqSwFastToggleDelayReserved;
	rand uvm_reg_field ACSMWckFreqSwFastToggleDelayReserved;
	rand uvm_reg_field ACSMWckFreqSwFastTogglePulse_p3_ACSMWckFreqSwFastToggleWidth;
	rand uvm_reg_field ACSMWckFreqSwFastToggleWidth;
	rand uvm_reg_field ACSMWckFreeRunMode_p3_ACSMWckFreeRunMode_p3;
	rand uvm_reg_field ACSMRptCntOverride_p3_ACSMRptCntOverride_p3;
	rand uvm_reg_field ACSMRptCntDbl_p3_ACSMRptCntDbl_p3;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	DfiCustMode_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB };
		option.weight = 1;
	}

	HwtMRL_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD };
		option.weight = 1;
	}

	PPTTrainSetup_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h40 };
		option.weight = 1;
	}

	PhyMstrFreqOverride_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h41 };
		option.weight = 1;
	}

	DfiHandshakeDelays0_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h66 };
		option.weight = 1;
	}

	DfiRespHandshakeDelays0_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h6B };
		option.weight = 1;
	}

	DfiHandshakeDelays1_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hE6 };
		option.weight = 1;
	}

	DfiRespHandshakeDelays1_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hEB };
		option.weight = 1;
	}

	PUBReservedP1_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFF };
		option.weight = 1;
	}

	ACSMStartAddr_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h122 };
		option.weight = 1;
	}

	ACSMStopAddr_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h123 };
		option.weight = 1;
	}

	ACSMRxEnPulse_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h12C };
		option.weight = 1;
	}

	ACSMRxValPulse_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h12D };
		option.weight = 1;
	}

	ACSMTxEnPulse_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h12E };
		option.weight = 1;
	}

	ACSMWrcsPulse_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h12F };
		option.weight = 1;
	}

	ACSMRdcsPulse_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h130 };
		option.weight = 1;
	}

	ACSMWckWriteStaticLoPulse_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h135 };
		option.weight = 1;
	}

	ACSMWckWriteStaticHiPulse_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h136 };
		option.weight = 1;
	}

	ACSMWckWriteTogglePulse_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h137 };
		option.weight = 1;
	}

	ACSMWckWriteFastTogglePulse_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h138 };
		option.weight = 1;
	}

	ACSMWckReadStaticLoPulse_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h139 };
		option.weight = 1;
	}

	ACSMWckReadStaticHiPulse_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h13A };
		option.weight = 1;
	}

	ACSMWckReadTogglePulse_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h13B };
		option.weight = 1;
	}

	ACSMWckReadFastTogglePulse_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h13C };
		option.weight = 1;
	}

	ACSMWckFreqSwStaticLoPulse_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h13D };
		option.weight = 1;
	}

	ACSMWckFreqSwStaticHiPulse_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h13E };
		option.weight = 1;
	}

	ACSMWckFreqSwTogglePulse_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h13F };
		option.weight = 1;
	}

	ACSMWckFreqSwFastTogglePulse_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h140 };
		option.weight = 1;
	}

	ACSMWckFreeRunMode_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h141 };
		option.weight = 1;
	}

	ACSMRptCntOverride_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h145 };
		option.weight = 1;
	}

	ACSMRptCntDbl_p3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h146 };
		option.weight = 1;
	}
endgroup
	function new(string name = "DWC_DDRPHYA_PPGC0_p3");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.DfiCustMode_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiCustMode_p3::type_id::create("DfiCustMode_p3",,get_full_name());
      if(this.DfiCustMode_p3.has_coverage(UVM_CVR_ALL))
      	this.DfiCustMode_p3.cg_bits.option.name = {get_name(), ".", "DfiCustMode_p3_bits"};
      this.DfiCustMode_p3.configure(this, null, "");
      this.DfiCustMode_p3.build();
      this.default_map.add_reg(this.DfiCustMode_p3, `UVM_REG_ADDR_WIDTH'hB, "RW", 0);
		this.DfiCustMode_p3_DfiCustMode_p3 = this.DfiCustMode_p3.DfiCustMode_p3;
      this.HwtMRL_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_HwtMRL_p3::type_id::create("HwtMRL_p3",,get_full_name());
      if(this.HwtMRL_p3.has_coverage(UVM_CVR_ALL))
      	this.HwtMRL_p3.cg_bits.option.name = {get_name(), ".", "HwtMRL_p3_bits"};
      this.HwtMRL_p3.configure(this, null, "");
      this.HwtMRL_p3.build();
      this.default_map.add_reg(this.HwtMRL_p3, `UVM_REG_ADDR_WIDTH'hD, "RW", 0);
		this.HwtMRL_p3_HwtMRL_p3 = this.HwtMRL_p3.HwtMRL_p3;
      this.PPTTrainSetup_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_PPTTrainSetup_p3::type_id::create("PPTTrainSetup_p3",,get_full_name());
      if(this.PPTTrainSetup_p3.has_coverage(UVM_CVR_ALL))
      	this.PPTTrainSetup_p3.cg_bits.option.name = {get_name(), ".", "PPTTrainSetup_p3_bits"};
      this.PPTTrainSetup_p3.configure(this, null, "");
      this.PPTTrainSetup_p3.build();
      this.default_map.add_reg(this.PPTTrainSetup_p3, `UVM_REG_ADDR_WIDTH'h40, "RW", 0);
		this.PPTTrainSetup_p3_PhyMstrTrainInterval = this.PPTTrainSetup_p3.PhyMstrTrainInterval;
		this.PhyMstrTrainInterval = this.PPTTrainSetup_p3.PhyMstrTrainInterval;
		this.PPTTrainSetup_p3_PhyMstrMaxReqToAck = this.PPTTrainSetup_p3.PhyMstrMaxReqToAck;
		this.PhyMstrMaxReqToAck = this.PPTTrainSetup_p3.PhyMstrMaxReqToAck;
      this.PhyMstrFreqOverride_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_PhyMstrFreqOverride_p3::type_id::create("PhyMstrFreqOverride_p3",,get_full_name());
      if(this.PhyMstrFreqOverride_p3.has_coverage(UVM_CVR_ALL))
      	this.PhyMstrFreqOverride_p3.cg_bits.option.name = {get_name(), ".", "PhyMstrFreqOverride_p3_bits"};
      this.PhyMstrFreqOverride_p3.configure(this, null, "");
      this.PhyMstrFreqOverride_p3.build();
      this.default_map.add_reg(this.PhyMstrFreqOverride_p3, `UVM_REG_ADDR_WIDTH'h41, "RW", 0);
		this.PhyMstrFreqOverride_p3_PhyMstrFreqOverride_p3 = this.PhyMstrFreqOverride_p3.PhyMstrFreqOverride_p3;
      this.DfiHandshakeDelays0_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiHandshakeDelays0_p3::type_id::create("DfiHandshakeDelays0_p3",,get_full_name());
      if(this.DfiHandshakeDelays0_p3.has_coverage(UVM_CVR_ALL))
      	this.DfiHandshakeDelays0_p3.cg_bits.option.name = {get_name(), ".", "DfiHandshakeDelays0_p3_bits"};
      this.DfiHandshakeDelays0_p3.configure(this, null, "");
      this.DfiHandshakeDelays0_p3.build();
      this.default_map.add_reg(this.DfiHandshakeDelays0_p3, `UVM_REG_ADDR_WIDTH'h66, "RW", 0);
		this.DfiHandshakeDelays0_p3_PhyUpdAckDelay0 = this.DfiHandshakeDelays0_p3.PhyUpdAckDelay0;
		this.PhyUpdAckDelay0 = this.DfiHandshakeDelays0_p3.PhyUpdAckDelay0;
		this.DfiHandshakeDelays0_p3_PhyUpdReqDelay0 = this.DfiHandshakeDelays0_p3.PhyUpdReqDelay0;
		this.PhyUpdReqDelay0 = this.DfiHandshakeDelays0_p3.PhyUpdReqDelay0;
		this.DfiHandshakeDelays0_p3_CtrlUpdReqDelay0 = this.DfiHandshakeDelays0_p3.CtrlUpdReqDelay0;
		this.CtrlUpdReqDelay0 = this.DfiHandshakeDelays0_p3.CtrlUpdReqDelay0;
      this.DfiRespHandshakeDelays0_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiRespHandshakeDelays0_p3::type_id::create("DfiRespHandshakeDelays0_p3",,get_full_name());
      if(this.DfiRespHandshakeDelays0_p3.has_coverage(UVM_CVR_ALL))
      	this.DfiRespHandshakeDelays0_p3.cg_bits.option.name = {get_name(), ".", "DfiRespHandshakeDelays0_p3_bits"};
      this.DfiRespHandshakeDelays0_p3.configure(this, null, "");
      this.DfiRespHandshakeDelays0_p3.build();
      this.default_map.add_reg(this.DfiRespHandshakeDelays0_p3, `UVM_REG_ADDR_WIDTH'h6B, "RW", 0);
		this.DfiRespHandshakeDelays0_p3_LpCtrlAckDelay0 = this.DfiRespHandshakeDelays0_p3.LpCtrlAckDelay0;
		this.LpCtrlAckDelay0 = this.DfiRespHandshakeDelays0_p3.LpCtrlAckDelay0;
		this.DfiRespHandshakeDelays0_p3_LpDataAckDelay0 = this.DfiRespHandshakeDelays0_p3.LpDataAckDelay0;
		this.LpDataAckDelay0 = this.DfiRespHandshakeDelays0_p3.LpDataAckDelay0;
		this.DfiRespHandshakeDelays0_p3_CtrlUpdAckDelay0 = this.DfiRespHandshakeDelays0_p3.CtrlUpdAckDelay0;
		this.CtrlUpdAckDelay0 = this.DfiRespHandshakeDelays0_p3.CtrlUpdAckDelay0;
		this.DfiRespHandshakeDelays0_p3_LpAssertAckDelay0 = this.DfiRespHandshakeDelays0_p3.LpAssertAckDelay0;
		this.LpAssertAckDelay0 = this.DfiRespHandshakeDelays0_p3.LpAssertAckDelay0;
      this.DfiHandshakeDelays1_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiHandshakeDelays1_p3::type_id::create("DfiHandshakeDelays1_p3",,get_full_name());
      if(this.DfiHandshakeDelays1_p3.has_coverage(UVM_CVR_ALL))
      	this.DfiHandshakeDelays1_p3.cg_bits.option.name = {get_name(), ".", "DfiHandshakeDelays1_p3_bits"};
      this.DfiHandshakeDelays1_p3.configure(this, null, "");
      this.DfiHandshakeDelays1_p3.build();
      this.default_map.add_reg(this.DfiHandshakeDelays1_p3, `UVM_REG_ADDR_WIDTH'hE6, "RW", 0);
		this.DfiHandshakeDelays1_p3_PhyUpdAckDelay1 = this.DfiHandshakeDelays1_p3.PhyUpdAckDelay1;
		this.PhyUpdAckDelay1 = this.DfiHandshakeDelays1_p3.PhyUpdAckDelay1;
		this.DfiHandshakeDelays1_p3_PhyUpdReqDelay1 = this.DfiHandshakeDelays1_p3.PhyUpdReqDelay1;
		this.PhyUpdReqDelay1 = this.DfiHandshakeDelays1_p3.PhyUpdReqDelay1;
		this.DfiHandshakeDelays1_p3_CtrlUpdReqDelay1 = this.DfiHandshakeDelays1_p3.CtrlUpdReqDelay1;
		this.CtrlUpdReqDelay1 = this.DfiHandshakeDelays1_p3.CtrlUpdReqDelay1;
      this.DfiRespHandshakeDelays1_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_DfiRespHandshakeDelays1_p3::type_id::create("DfiRespHandshakeDelays1_p3",,get_full_name());
      if(this.DfiRespHandshakeDelays1_p3.has_coverage(UVM_CVR_ALL))
      	this.DfiRespHandshakeDelays1_p3.cg_bits.option.name = {get_name(), ".", "DfiRespHandshakeDelays1_p3_bits"};
      this.DfiRespHandshakeDelays1_p3.configure(this, null, "");
      this.DfiRespHandshakeDelays1_p3.build();
      this.default_map.add_reg(this.DfiRespHandshakeDelays1_p3, `UVM_REG_ADDR_WIDTH'hEB, "RW", 0);
		this.DfiRespHandshakeDelays1_p3_LpCtrlAckDelay1 = this.DfiRespHandshakeDelays1_p3.LpCtrlAckDelay1;
		this.LpCtrlAckDelay1 = this.DfiRespHandshakeDelays1_p3.LpCtrlAckDelay1;
		this.DfiRespHandshakeDelays1_p3_LpDataAckDelay1 = this.DfiRespHandshakeDelays1_p3.LpDataAckDelay1;
		this.LpDataAckDelay1 = this.DfiRespHandshakeDelays1_p3.LpDataAckDelay1;
		this.DfiRespHandshakeDelays1_p3_CtrlUpdAckDelay1 = this.DfiRespHandshakeDelays1_p3.CtrlUpdAckDelay1;
		this.CtrlUpdAckDelay1 = this.DfiRespHandshakeDelays1_p3.CtrlUpdAckDelay1;
		this.DfiRespHandshakeDelays1_p3_LpAssertAckDelay1 = this.DfiRespHandshakeDelays1_p3.LpAssertAckDelay1;
		this.LpAssertAckDelay1 = this.DfiRespHandshakeDelays1_p3.LpAssertAckDelay1;
      this.PUBReservedP1_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_PUBReservedP1_p3::type_id::create("PUBReservedP1_p3",,get_full_name());
      if(this.PUBReservedP1_p3.has_coverage(UVM_CVR_ALL))
      	this.PUBReservedP1_p3.cg_bits.option.name = {get_name(), ".", "PUBReservedP1_p3_bits"};
      this.PUBReservedP1_p3.configure(this, null, "");
      this.PUBReservedP1_p3.build();
      this.default_map.add_reg(this.PUBReservedP1_p3, `UVM_REG_ADDR_WIDTH'hFF, "RW", 0);
		this.PUBReservedP1_p3_PUBReservedP1_p3 = this.PUBReservedP1_p3.PUBReservedP1_p3;
      this.ACSMStartAddr_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMStartAddr_p3::type_id::create("ACSMStartAddr_p3",,get_full_name());
      if(this.ACSMStartAddr_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMStartAddr_p3.cg_bits.option.name = {get_name(), ".", "ACSMStartAddr_p3_bits"};
      this.ACSMStartAddr_p3.configure(this, null, "");
      this.ACSMStartAddr_p3.build();
      this.default_map.add_reg(this.ACSMStartAddr_p3, `UVM_REG_ADDR_WIDTH'h122, "RW", 0);
		this.ACSMStartAddr_p3_ACSMStartAddr_p3 = this.ACSMStartAddr_p3.ACSMStartAddr_p3;
      this.ACSMStopAddr_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMStopAddr_p3::type_id::create("ACSMStopAddr_p3",,get_full_name());
      if(this.ACSMStopAddr_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMStopAddr_p3.cg_bits.option.name = {get_name(), ".", "ACSMStopAddr_p3_bits"};
      this.ACSMStopAddr_p3.configure(this, null, "");
      this.ACSMStopAddr_p3.build();
      this.default_map.add_reg(this.ACSMStopAddr_p3, `UVM_REG_ADDR_WIDTH'h123, "RW", 0);
		this.ACSMStopAddr_p3_ACSMStopAddr_p3 = this.ACSMStopAddr_p3.ACSMStopAddr_p3;
      this.ACSMRxEnPulse_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRxEnPulse_p3::type_id::create("ACSMRxEnPulse_p3",,get_full_name());
      if(this.ACSMRxEnPulse_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMRxEnPulse_p3.cg_bits.option.name = {get_name(), ".", "ACSMRxEnPulse_p3_bits"};
      this.ACSMRxEnPulse_p3.configure(this, null, "");
      this.ACSMRxEnPulse_p3.build();
      this.default_map.add_reg(this.ACSMRxEnPulse_p3, `UVM_REG_ADDR_WIDTH'h12C, "RW", 0);
		this.ACSMRxEnPulse_p3_ACSMRxEnDelay = this.ACSMRxEnPulse_p3.ACSMRxEnDelay;
		this.ACSMRxEnDelay = this.ACSMRxEnPulse_p3.ACSMRxEnDelay;
		this.ACSMRxEnPulse_p3_ACSMRxEnDelayReserved = this.ACSMRxEnPulse_p3.ACSMRxEnDelayReserved;
		this.ACSMRxEnDelayReserved = this.ACSMRxEnPulse_p3.ACSMRxEnDelayReserved;
		this.ACSMRxEnPulse_p3_ACSMRxEnWidth = this.ACSMRxEnPulse_p3.ACSMRxEnWidth;
		this.ACSMRxEnWidth = this.ACSMRxEnPulse_p3.ACSMRxEnWidth;
      this.ACSMRxValPulse_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRxValPulse_p3::type_id::create("ACSMRxValPulse_p3",,get_full_name());
      if(this.ACSMRxValPulse_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMRxValPulse_p3.cg_bits.option.name = {get_name(), ".", "ACSMRxValPulse_p3_bits"};
      this.ACSMRxValPulse_p3.configure(this, null, "");
      this.ACSMRxValPulse_p3.build();
      this.default_map.add_reg(this.ACSMRxValPulse_p3, `UVM_REG_ADDR_WIDTH'h12D, "RW", 0);
		this.ACSMRxValPulse_p3_ACSMRxValDelay = this.ACSMRxValPulse_p3.ACSMRxValDelay;
		this.ACSMRxValDelay = this.ACSMRxValPulse_p3.ACSMRxValDelay;
		this.ACSMRxValPulse_p3_ACSMRxValDelayReserved = this.ACSMRxValPulse_p3.ACSMRxValDelayReserved;
		this.ACSMRxValDelayReserved = this.ACSMRxValPulse_p3.ACSMRxValDelayReserved;
		this.ACSMRxValPulse_p3_ACSMRxValWidth = this.ACSMRxValPulse_p3.ACSMRxValWidth;
		this.ACSMRxValWidth = this.ACSMRxValPulse_p3.ACSMRxValWidth;
      this.ACSMTxEnPulse_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMTxEnPulse_p3::type_id::create("ACSMTxEnPulse_p3",,get_full_name());
      if(this.ACSMTxEnPulse_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMTxEnPulse_p3.cg_bits.option.name = {get_name(), ".", "ACSMTxEnPulse_p3_bits"};
      this.ACSMTxEnPulse_p3.configure(this, null, "");
      this.ACSMTxEnPulse_p3.build();
      this.default_map.add_reg(this.ACSMTxEnPulse_p3, `UVM_REG_ADDR_WIDTH'h12E, "RW", 0);
		this.ACSMTxEnPulse_p3_ACSMTxEnDelay = this.ACSMTxEnPulse_p3.ACSMTxEnDelay;
		this.ACSMTxEnDelay = this.ACSMTxEnPulse_p3.ACSMTxEnDelay;
		this.ACSMTxEnPulse_p3_ACSMTxEnDelayReserved = this.ACSMTxEnPulse_p3.ACSMTxEnDelayReserved;
		this.ACSMTxEnDelayReserved = this.ACSMTxEnPulse_p3.ACSMTxEnDelayReserved;
		this.ACSMTxEnPulse_p3_ACSMTxEnWidth = this.ACSMTxEnPulse_p3.ACSMTxEnWidth;
		this.ACSMTxEnWidth = this.ACSMTxEnPulse_p3.ACSMTxEnWidth;
      this.ACSMWrcsPulse_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWrcsPulse_p3::type_id::create("ACSMWrcsPulse_p3",,get_full_name());
      if(this.ACSMWrcsPulse_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMWrcsPulse_p3.cg_bits.option.name = {get_name(), ".", "ACSMWrcsPulse_p3_bits"};
      this.ACSMWrcsPulse_p3.configure(this, null, "");
      this.ACSMWrcsPulse_p3.build();
      this.default_map.add_reg(this.ACSMWrcsPulse_p3, `UVM_REG_ADDR_WIDTH'h12F, "RW", 0);
		this.ACSMWrcsPulse_p3_ACSMWrcsDelay = this.ACSMWrcsPulse_p3.ACSMWrcsDelay;
		this.ACSMWrcsDelay = this.ACSMWrcsPulse_p3.ACSMWrcsDelay;
		this.ACSMWrcsPulse_p3_ACSMWrcsDelayReserved = this.ACSMWrcsPulse_p3.ACSMWrcsDelayReserved;
		this.ACSMWrcsDelayReserved = this.ACSMWrcsPulse_p3.ACSMWrcsDelayReserved;
		this.ACSMWrcsPulse_p3_ACSMWrcsWidth = this.ACSMWrcsPulse_p3.ACSMWrcsWidth;
		this.ACSMWrcsWidth = this.ACSMWrcsPulse_p3.ACSMWrcsWidth;
      this.ACSMRdcsPulse_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRdcsPulse_p3::type_id::create("ACSMRdcsPulse_p3",,get_full_name());
      if(this.ACSMRdcsPulse_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMRdcsPulse_p3.cg_bits.option.name = {get_name(), ".", "ACSMRdcsPulse_p3_bits"};
      this.ACSMRdcsPulse_p3.configure(this, null, "");
      this.ACSMRdcsPulse_p3.build();
      this.default_map.add_reg(this.ACSMRdcsPulse_p3, `UVM_REG_ADDR_WIDTH'h130, "RW", 0);
		this.ACSMRdcsPulse_p3_ACSMRdcsDelay = this.ACSMRdcsPulse_p3.ACSMRdcsDelay;
		this.ACSMRdcsDelay = this.ACSMRdcsPulse_p3.ACSMRdcsDelay;
		this.ACSMRdcsPulse_p3_ACSMRdcsDelayReserved = this.ACSMRdcsPulse_p3.ACSMRdcsDelayReserved;
		this.ACSMRdcsDelayReserved = this.ACSMRdcsPulse_p3.ACSMRdcsDelayReserved;
		this.ACSMRdcsPulse_p3_ACSMRdcsWidth = this.ACSMRdcsPulse_p3.ACSMRdcsWidth;
		this.ACSMRdcsWidth = this.ACSMRdcsPulse_p3.ACSMRdcsWidth;
      this.ACSMWckWriteStaticLoPulse_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteStaticLoPulse_p3::type_id::create("ACSMWckWriteStaticLoPulse_p3",,get_full_name());
      if(this.ACSMWckWriteStaticLoPulse_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckWriteStaticLoPulse_p3.cg_bits.option.name = {get_name(), ".", "ACSMWckWriteStaticLoPulse_p3_bits"};
      this.ACSMWckWriteStaticLoPulse_p3.configure(this, null, "");
      this.ACSMWckWriteStaticLoPulse_p3.build();
      this.default_map.add_reg(this.ACSMWckWriteStaticLoPulse_p3, `UVM_REG_ADDR_WIDTH'h135, "RW", 0);
		this.ACSMWckWriteStaticLoPulse_p3_ACSMWckWriteStaticLoDelay = this.ACSMWckWriteStaticLoPulse_p3.ACSMWckWriteStaticLoDelay;
		this.ACSMWckWriteStaticLoDelay = this.ACSMWckWriteStaticLoPulse_p3.ACSMWckWriteStaticLoDelay;
		this.ACSMWckWriteStaticLoPulse_p3_ACSMWckWriteStaticLoDelayReserved = this.ACSMWckWriteStaticLoPulse_p3.ACSMWckWriteStaticLoDelayReserved;
		this.ACSMWckWriteStaticLoDelayReserved = this.ACSMWckWriteStaticLoPulse_p3.ACSMWckWriteStaticLoDelayReserved;
		this.ACSMWckWriteStaticLoPulse_p3_ACSMWckWriteStaticLoWidth = this.ACSMWckWriteStaticLoPulse_p3.ACSMWckWriteStaticLoWidth;
		this.ACSMWckWriteStaticLoWidth = this.ACSMWckWriteStaticLoPulse_p3.ACSMWckWriteStaticLoWidth;
      this.ACSMWckWriteStaticHiPulse_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteStaticHiPulse_p3::type_id::create("ACSMWckWriteStaticHiPulse_p3",,get_full_name());
      if(this.ACSMWckWriteStaticHiPulse_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckWriteStaticHiPulse_p3.cg_bits.option.name = {get_name(), ".", "ACSMWckWriteStaticHiPulse_p3_bits"};
      this.ACSMWckWriteStaticHiPulse_p3.configure(this, null, "");
      this.ACSMWckWriteStaticHiPulse_p3.build();
      this.default_map.add_reg(this.ACSMWckWriteStaticHiPulse_p3, `UVM_REG_ADDR_WIDTH'h136, "RW", 0);
		this.ACSMWckWriteStaticHiPulse_p3_ACSMWckWriteStaticHiDelay = this.ACSMWckWriteStaticHiPulse_p3.ACSMWckWriteStaticHiDelay;
		this.ACSMWckWriteStaticHiDelay = this.ACSMWckWriteStaticHiPulse_p3.ACSMWckWriteStaticHiDelay;
		this.ACSMWckWriteStaticHiPulse_p3_ACSMWckWriteStaticHiDelayReserved = this.ACSMWckWriteStaticHiPulse_p3.ACSMWckWriteStaticHiDelayReserved;
		this.ACSMWckWriteStaticHiDelayReserved = this.ACSMWckWriteStaticHiPulse_p3.ACSMWckWriteStaticHiDelayReserved;
		this.ACSMWckWriteStaticHiPulse_p3_ACSMWckWriteStaticHiWidth = this.ACSMWckWriteStaticHiPulse_p3.ACSMWckWriteStaticHiWidth;
		this.ACSMWckWriteStaticHiWidth = this.ACSMWckWriteStaticHiPulse_p3.ACSMWckWriteStaticHiWidth;
      this.ACSMWckWriteTogglePulse_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteTogglePulse_p3::type_id::create("ACSMWckWriteTogglePulse_p3",,get_full_name());
      if(this.ACSMWckWriteTogglePulse_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckWriteTogglePulse_p3.cg_bits.option.name = {get_name(), ".", "ACSMWckWriteTogglePulse_p3_bits"};
      this.ACSMWckWriteTogglePulse_p3.configure(this, null, "");
      this.ACSMWckWriteTogglePulse_p3.build();
      this.default_map.add_reg(this.ACSMWckWriteTogglePulse_p3, `UVM_REG_ADDR_WIDTH'h137, "RW", 0);
		this.ACSMWckWriteTogglePulse_p3_ACSMWckWriteToggleDelay = this.ACSMWckWriteTogglePulse_p3.ACSMWckWriteToggleDelay;
		this.ACSMWckWriteToggleDelay = this.ACSMWckWriteTogglePulse_p3.ACSMWckWriteToggleDelay;
		this.ACSMWckWriteTogglePulse_p3_ACSMWckWriteToggleDelayReserved = this.ACSMWckWriteTogglePulse_p3.ACSMWckWriteToggleDelayReserved;
		this.ACSMWckWriteToggleDelayReserved = this.ACSMWckWriteTogglePulse_p3.ACSMWckWriteToggleDelayReserved;
		this.ACSMWckWriteTogglePulse_p3_ACSMWckWriteToggleWidth = this.ACSMWckWriteTogglePulse_p3.ACSMWckWriteToggleWidth;
		this.ACSMWckWriteToggleWidth = this.ACSMWckWriteTogglePulse_p3.ACSMWckWriteToggleWidth;
      this.ACSMWckWriteFastTogglePulse_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckWriteFastTogglePulse_p3::type_id::create("ACSMWckWriteFastTogglePulse_p3",,get_full_name());
      if(this.ACSMWckWriteFastTogglePulse_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckWriteFastTogglePulse_p3.cg_bits.option.name = {get_name(), ".", "ACSMWckWriteFastTogglePulse_p3_bits"};
      this.ACSMWckWriteFastTogglePulse_p3.configure(this, null, "");
      this.ACSMWckWriteFastTogglePulse_p3.build();
      this.default_map.add_reg(this.ACSMWckWriteFastTogglePulse_p3, `UVM_REG_ADDR_WIDTH'h138, "RW", 0);
		this.ACSMWckWriteFastTogglePulse_p3_ACSMWckWriteFastToggleDelay = this.ACSMWckWriteFastTogglePulse_p3.ACSMWckWriteFastToggleDelay;
		this.ACSMWckWriteFastToggleDelay = this.ACSMWckWriteFastTogglePulse_p3.ACSMWckWriteFastToggleDelay;
		this.ACSMWckWriteFastTogglePulse_p3_ACSMWckWriteFastToggleDelayReserved = this.ACSMWckWriteFastTogglePulse_p3.ACSMWckWriteFastToggleDelayReserved;
		this.ACSMWckWriteFastToggleDelayReserved = this.ACSMWckWriteFastTogglePulse_p3.ACSMWckWriteFastToggleDelayReserved;
		this.ACSMWckWriteFastTogglePulse_p3_ACSMWckWriteFastToggleWidth = this.ACSMWckWriteFastTogglePulse_p3.ACSMWckWriteFastToggleWidth;
		this.ACSMWckWriteFastToggleWidth = this.ACSMWckWriteFastTogglePulse_p3.ACSMWckWriteFastToggleWidth;
      this.ACSMWckReadStaticLoPulse_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckReadStaticLoPulse_p3::type_id::create("ACSMWckReadStaticLoPulse_p3",,get_full_name());
      if(this.ACSMWckReadStaticLoPulse_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckReadStaticLoPulse_p3.cg_bits.option.name = {get_name(), ".", "ACSMWckReadStaticLoPulse_p3_bits"};
      this.ACSMWckReadStaticLoPulse_p3.configure(this, null, "");
      this.ACSMWckReadStaticLoPulse_p3.build();
      this.default_map.add_reg(this.ACSMWckReadStaticLoPulse_p3, `UVM_REG_ADDR_WIDTH'h139, "RW", 0);
		this.ACSMWckReadStaticLoPulse_p3_ACSMWckReadStaticLoDelay = this.ACSMWckReadStaticLoPulse_p3.ACSMWckReadStaticLoDelay;
		this.ACSMWckReadStaticLoDelay = this.ACSMWckReadStaticLoPulse_p3.ACSMWckReadStaticLoDelay;
		this.ACSMWckReadStaticLoPulse_p3_ACSMWckReadStaticLoDelayReserved = this.ACSMWckReadStaticLoPulse_p3.ACSMWckReadStaticLoDelayReserved;
		this.ACSMWckReadStaticLoDelayReserved = this.ACSMWckReadStaticLoPulse_p3.ACSMWckReadStaticLoDelayReserved;
		this.ACSMWckReadStaticLoPulse_p3_ACSMWckReadStaticLoWidth = this.ACSMWckReadStaticLoPulse_p3.ACSMWckReadStaticLoWidth;
		this.ACSMWckReadStaticLoWidth = this.ACSMWckReadStaticLoPulse_p3.ACSMWckReadStaticLoWidth;
      this.ACSMWckReadStaticHiPulse_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckReadStaticHiPulse_p3::type_id::create("ACSMWckReadStaticHiPulse_p3",,get_full_name());
      if(this.ACSMWckReadStaticHiPulse_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckReadStaticHiPulse_p3.cg_bits.option.name = {get_name(), ".", "ACSMWckReadStaticHiPulse_p3_bits"};
      this.ACSMWckReadStaticHiPulse_p3.configure(this, null, "");
      this.ACSMWckReadStaticHiPulse_p3.build();
      this.default_map.add_reg(this.ACSMWckReadStaticHiPulse_p3, `UVM_REG_ADDR_WIDTH'h13A, "RW", 0);
		this.ACSMWckReadStaticHiPulse_p3_ACSMWckReadStaticHiDelay = this.ACSMWckReadStaticHiPulse_p3.ACSMWckReadStaticHiDelay;
		this.ACSMWckReadStaticHiDelay = this.ACSMWckReadStaticHiPulse_p3.ACSMWckReadStaticHiDelay;
		this.ACSMWckReadStaticHiPulse_p3_ACSMWckReadStaticHiDelayReserved = this.ACSMWckReadStaticHiPulse_p3.ACSMWckReadStaticHiDelayReserved;
		this.ACSMWckReadStaticHiDelayReserved = this.ACSMWckReadStaticHiPulse_p3.ACSMWckReadStaticHiDelayReserved;
		this.ACSMWckReadStaticHiPulse_p3_ACSMWckReadStaticHiWidth = this.ACSMWckReadStaticHiPulse_p3.ACSMWckReadStaticHiWidth;
		this.ACSMWckReadStaticHiWidth = this.ACSMWckReadStaticHiPulse_p3.ACSMWckReadStaticHiWidth;
      this.ACSMWckReadTogglePulse_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckReadTogglePulse_p3::type_id::create("ACSMWckReadTogglePulse_p3",,get_full_name());
      if(this.ACSMWckReadTogglePulse_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckReadTogglePulse_p3.cg_bits.option.name = {get_name(), ".", "ACSMWckReadTogglePulse_p3_bits"};
      this.ACSMWckReadTogglePulse_p3.configure(this, null, "");
      this.ACSMWckReadTogglePulse_p3.build();
      this.default_map.add_reg(this.ACSMWckReadTogglePulse_p3, `UVM_REG_ADDR_WIDTH'h13B, "RW", 0);
		this.ACSMWckReadTogglePulse_p3_ACSMWckReadToggleDelay = this.ACSMWckReadTogglePulse_p3.ACSMWckReadToggleDelay;
		this.ACSMWckReadToggleDelay = this.ACSMWckReadTogglePulse_p3.ACSMWckReadToggleDelay;
		this.ACSMWckReadTogglePulse_p3_ACSMWckReadToggleDelayReserved = this.ACSMWckReadTogglePulse_p3.ACSMWckReadToggleDelayReserved;
		this.ACSMWckReadToggleDelayReserved = this.ACSMWckReadTogglePulse_p3.ACSMWckReadToggleDelayReserved;
		this.ACSMWckReadTogglePulse_p3_ACSMWckReadToggleWidth = this.ACSMWckReadTogglePulse_p3.ACSMWckReadToggleWidth;
		this.ACSMWckReadToggleWidth = this.ACSMWckReadTogglePulse_p3.ACSMWckReadToggleWidth;
      this.ACSMWckReadFastTogglePulse_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckReadFastTogglePulse_p3::type_id::create("ACSMWckReadFastTogglePulse_p3",,get_full_name());
      if(this.ACSMWckReadFastTogglePulse_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckReadFastTogglePulse_p3.cg_bits.option.name = {get_name(), ".", "ACSMWckReadFastTogglePulse_p3_bits"};
      this.ACSMWckReadFastTogglePulse_p3.configure(this, null, "");
      this.ACSMWckReadFastTogglePulse_p3.build();
      this.default_map.add_reg(this.ACSMWckReadFastTogglePulse_p3, `UVM_REG_ADDR_WIDTH'h13C, "RW", 0);
		this.ACSMWckReadFastTogglePulse_p3_ACSMWckReadFastToggleDelay = this.ACSMWckReadFastTogglePulse_p3.ACSMWckReadFastToggleDelay;
		this.ACSMWckReadFastToggleDelay = this.ACSMWckReadFastTogglePulse_p3.ACSMWckReadFastToggleDelay;
		this.ACSMWckReadFastTogglePulse_p3_ACSMWckReadFastToggleDelayReserved = this.ACSMWckReadFastTogglePulse_p3.ACSMWckReadFastToggleDelayReserved;
		this.ACSMWckReadFastToggleDelayReserved = this.ACSMWckReadFastTogglePulse_p3.ACSMWckReadFastToggleDelayReserved;
		this.ACSMWckReadFastTogglePulse_p3_ACSMWckReadFastToggleWidth = this.ACSMWckReadFastTogglePulse_p3.ACSMWckReadFastToggleWidth;
		this.ACSMWckReadFastToggleWidth = this.ACSMWckReadFastTogglePulse_p3.ACSMWckReadFastToggleWidth;
      this.ACSMWckFreqSwStaticLoPulse_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwStaticLoPulse_p3::type_id::create("ACSMWckFreqSwStaticLoPulse_p3",,get_full_name());
      if(this.ACSMWckFreqSwStaticLoPulse_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckFreqSwStaticLoPulse_p3.cg_bits.option.name = {get_name(), ".", "ACSMWckFreqSwStaticLoPulse_p3_bits"};
      this.ACSMWckFreqSwStaticLoPulse_p3.configure(this, null, "");
      this.ACSMWckFreqSwStaticLoPulse_p3.build();
      this.default_map.add_reg(this.ACSMWckFreqSwStaticLoPulse_p3, `UVM_REG_ADDR_WIDTH'h13D, "RW", 0);
		this.ACSMWckFreqSwStaticLoPulse_p3_ACSMWckFreqSwStaticLoDelay = this.ACSMWckFreqSwStaticLoPulse_p3.ACSMWckFreqSwStaticLoDelay;
		this.ACSMWckFreqSwStaticLoDelay = this.ACSMWckFreqSwStaticLoPulse_p3.ACSMWckFreqSwStaticLoDelay;
		this.ACSMWckFreqSwStaticLoPulse_p3_ACSMWckFreqSwStaticLoDelayReserved = this.ACSMWckFreqSwStaticLoPulse_p3.ACSMWckFreqSwStaticLoDelayReserved;
		this.ACSMWckFreqSwStaticLoDelayReserved = this.ACSMWckFreqSwStaticLoPulse_p3.ACSMWckFreqSwStaticLoDelayReserved;
		this.ACSMWckFreqSwStaticLoPulse_p3_ACSMWckFreqSwStaticLoWidth = this.ACSMWckFreqSwStaticLoPulse_p3.ACSMWckFreqSwStaticLoWidth;
		this.ACSMWckFreqSwStaticLoWidth = this.ACSMWckFreqSwStaticLoPulse_p3.ACSMWckFreqSwStaticLoWidth;
      this.ACSMWckFreqSwStaticHiPulse_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwStaticHiPulse_p3::type_id::create("ACSMWckFreqSwStaticHiPulse_p3",,get_full_name());
      if(this.ACSMWckFreqSwStaticHiPulse_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckFreqSwStaticHiPulse_p3.cg_bits.option.name = {get_name(), ".", "ACSMWckFreqSwStaticHiPulse_p3_bits"};
      this.ACSMWckFreqSwStaticHiPulse_p3.configure(this, null, "");
      this.ACSMWckFreqSwStaticHiPulse_p3.build();
      this.default_map.add_reg(this.ACSMWckFreqSwStaticHiPulse_p3, `UVM_REG_ADDR_WIDTH'h13E, "RW", 0);
		this.ACSMWckFreqSwStaticHiPulse_p3_ACSMWckFreqSwStaticHiDelay = this.ACSMWckFreqSwStaticHiPulse_p3.ACSMWckFreqSwStaticHiDelay;
		this.ACSMWckFreqSwStaticHiDelay = this.ACSMWckFreqSwStaticHiPulse_p3.ACSMWckFreqSwStaticHiDelay;
		this.ACSMWckFreqSwStaticHiPulse_p3_ACSMWckFreqSwStaticHiDelayReserved = this.ACSMWckFreqSwStaticHiPulse_p3.ACSMWckFreqSwStaticHiDelayReserved;
		this.ACSMWckFreqSwStaticHiDelayReserved = this.ACSMWckFreqSwStaticHiPulse_p3.ACSMWckFreqSwStaticHiDelayReserved;
		this.ACSMWckFreqSwStaticHiPulse_p3_ACSMWckFreqSwStaticHiWidth = this.ACSMWckFreqSwStaticHiPulse_p3.ACSMWckFreqSwStaticHiWidth;
		this.ACSMWckFreqSwStaticHiWidth = this.ACSMWckFreqSwStaticHiPulse_p3.ACSMWckFreqSwStaticHiWidth;
      this.ACSMWckFreqSwTogglePulse_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwTogglePulse_p3::type_id::create("ACSMWckFreqSwTogglePulse_p3",,get_full_name());
      if(this.ACSMWckFreqSwTogglePulse_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckFreqSwTogglePulse_p3.cg_bits.option.name = {get_name(), ".", "ACSMWckFreqSwTogglePulse_p3_bits"};
      this.ACSMWckFreqSwTogglePulse_p3.configure(this, null, "");
      this.ACSMWckFreqSwTogglePulse_p3.build();
      this.default_map.add_reg(this.ACSMWckFreqSwTogglePulse_p3, `UVM_REG_ADDR_WIDTH'h13F, "RW", 0);
		this.ACSMWckFreqSwTogglePulse_p3_ACSMWckFreqSwToggleDelay = this.ACSMWckFreqSwTogglePulse_p3.ACSMWckFreqSwToggleDelay;
		this.ACSMWckFreqSwToggleDelay = this.ACSMWckFreqSwTogglePulse_p3.ACSMWckFreqSwToggleDelay;
		this.ACSMWckFreqSwTogglePulse_p3_ACSMWckFreqSwToggleDelayReserved = this.ACSMWckFreqSwTogglePulse_p3.ACSMWckFreqSwToggleDelayReserved;
		this.ACSMWckFreqSwToggleDelayReserved = this.ACSMWckFreqSwTogglePulse_p3.ACSMWckFreqSwToggleDelayReserved;
		this.ACSMWckFreqSwTogglePulse_p3_ACSMWckFreqSwToggleWidth = this.ACSMWckFreqSwTogglePulse_p3.ACSMWckFreqSwToggleWidth;
		this.ACSMWckFreqSwToggleWidth = this.ACSMWckFreqSwTogglePulse_p3.ACSMWckFreqSwToggleWidth;
      this.ACSMWckFreqSwFastTogglePulse_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreqSwFastTogglePulse_p3::type_id::create("ACSMWckFreqSwFastTogglePulse_p3",,get_full_name());
      if(this.ACSMWckFreqSwFastTogglePulse_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckFreqSwFastTogglePulse_p3.cg_bits.option.name = {get_name(), ".", "ACSMWckFreqSwFastTogglePulse_p3_bits"};
      this.ACSMWckFreqSwFastTogglePulse_p3.configure(this, null, "");
      this.ACSMWckFreqSwFastTogglePulse_p3.build();
      this.default_map.add_reg(this.ACSMWckFreqSwFastTogglePulse_p3, `UVM_REG_ADDR_WIDTH'h140, "RW", 0);
		this.ACSMWckFreqSwFastTogglePulse_p3_ACSMWckFreqSwFastToggleDelay = this.ACSMWckFreqSwFastTogglePulse_p3.ACSMWckFreqSwFastToggleDelay;
		this.ACSMWckFreqSwFastToggleDelay = this.ACSMWckFreqSwFastTogglePulse_p3.ACSMWckFreqSwFastToggleDelay;
		this.ACSMWckFreqSwFastTogglePulse_p3_ACSMWckFreqSwFastToggleDelayReserved = this.ACSMWckFreqSwFastTogglePulse_p3.ACSMWckFreqSwFastToggleDelayReserved;
		this.ACSMWckFreqSwFastToggleDelayReserved = this.ACSMWckFreqSwFastTogglePulse_p3.ACSMWckFreqSwFastToggleDelayReserved;
		this.ACSMWckFreqSwFastTogglePulse_p3_ACSMWckFreqSwFastToggleWidth = this.ACSMWckFreqSwFastTogglePulse_p3.ACSMWckFreqSwFastToggleWidth;
		this.ACSMWckFreqSwFastToggleWidth = this.ACSMWckFreqSwFastTogglePulse_p3.ACSMWckFreqSwFastToggleWidth;
      this.ACSMWckFreeRunMode_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMWckFreeRunMode_p3::type_id::create("ACSMWckFreeRunMode_p3",,get_full_name());
      if(this.ACSMWckFreeRunMode_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckFreeRunMode_p3.cg_bits.option.name = {get_name(), ".", "ACSMWckFreeRunMode_p3_bits"};
      this.ACSMWckFreeRunMode_p3.configure(this, null, "");
      this.ACSMWckFreeRunMode_p3.build();
      this.default_map.add_reg(this.ACSMWckFreeRunMode_p3, `UVM_REG_ADDR_WIDTH'h141, "RW", 0);
		this.ACSMWckFreeRunMode_p3_ACSMWckFreeRunMode_p3 = this.ACSMWckFreeRunMode_p3.ACSMWckFreeRunMode_p3;
      this.ACSMRptCntOverride_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRptCntOverride_p3::type_id::create("ACSMRptCntOverride_p3",,get_full_name());
      if(this.ACSMRptCntOverride_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMRptCntOverride_p3.cg_bits.option.name = {get_name(), ".", "ACSMRptCntOverride_p3_bits"};
      this.ACSMRptCntOverride_p3.configure(this, null, "");
      this.ACSMRptCntOverride_p3.build();
      this.default_map.add_reg(this.ACSMRptCntOverride_p3, `UVM_REG_ADDR_WIDTH'h145, "RW", 0);
		this.ACSMRptCntOverride_p3_ACSMRptCntOverride_p3 = this.ACSMRptCntOverride_p3.ACSMRptCntOverride_p3;
      this.ACSMRptCntDbl_p3 = ral_reg_DWC_DDRPHYA_PPGC0_p3_ACSMRptCntDbl_p3::type_id::create("ACSMRptCntDbl_p3",,get_full_name());
      if(this.ACSMRptCntDbl_p3.has_coverage(UVM_CVR_ALL))
      	this.ACSMRptCntDbl_p3.cg_bits.option.name = {get_name(), ".", "ACSMRptCntDbl_p3_bits"};
      this.ACSMRptCntDbl_p3.configure(this, null, "");
      this.ACSMRptCntDbl_p3.build();
      this.default_map.add_reg(this.ACSMRptCntDbl_p3, `UVM_REG_ADDR_WIDTH'h146, "RW", 0);
		this.ACSMRptCntDbl_p3_ACSMRptCntDbl_p3 = this.ACSMRptCntDbl_p3.ACSMRptCntDbl_p3;
   endfunction : build

	`uvm_object_utils(ral_block_DWC_DDRPHYA_PPGC0_p3)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_DDRPHYA_PPGC0_p3


endpackage
`endif
