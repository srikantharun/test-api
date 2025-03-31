`ifndef RAL_DWC_DDRPHYA_PPGC0_P2_PKG
`define RAL_DWC_DDRPHYA_PPGC0_P2_PKG

package ral_DWC_DDRPHYA_PPGC0_p2_pkg;
import uvm_pkg::*;

class ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiCustMode_p2 extends uvm_reg;
	rand uvm_reg_field DfiCustMode_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiCustMode_p2: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_DfiCustMode_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiCustMode_p2 = uvm_reg_field::type_id::create("DfiCustMode_p2",,get_full_name());
      this.DfiCustMode_p2.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiCustMode_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiCustMode_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_HwtMRL_p2 extends uvm_reg;
	rand uvm_reg_field HwtMRL_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HwtMRL_p2: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_HwtMRL_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HwtMRL_p2 = uvm_reg_field::type_id::create("HwtMRL_p2",,get_full_name());
      this.HwtMRL_p2.configure(this, 6, 0, "RW", 0, 6'h6, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_HwtMRL_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_HwtMRL_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_PPTTrainSetup_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_PPTTrainSetup_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_PPTTrainSetup_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_PPTTrainSetup_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_PhyMstrFreqOverride_p2 extends uvm_reg;
	rand uvm_reg_field PhyMstrFreqOverride_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PhyMstrFreqOverride_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_PhyMstrFreqOverride_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PhyMstrFreqOverride_p2 = uvm_reg_field::type_id::create("PhyMstrFreqOverride_p2",,get_full_name());
      this.PhyMstrFreqOverride_p2.configure(this, 5, 0, "RW", 0, 5'h2, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_PhyMstrFreqOverride_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_PhyMstrFreqOverride_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiHandshakeDelays0_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_DfiHandshakeDelays0_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiHandshakeDelays0_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiHandshakeDelays0_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiRespHandshakeDelays0_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_DfiRespHandshakeDelays0_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiRespHandshakeDelays0_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiRespHandshakeDelays0_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiHandshakeDelays1_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_DfiHandshakeDelays1_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiHandshakeDelays1_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiHandshakeDelays1_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiRespHandshakeDelays1_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_DfiRespHandshakeDelays1_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiRespHandshakeDelays1_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiRespHandshakeDelays1_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_PUBReservedP1_p2 extends uvm_reg;
	rand uvm_reg_field PUBReservedP1_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PUBReservedP1_p2: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_PUBReservedP1_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PUBReservedP1_p2 = uvm_reg_field::type_id::create("PUBReservedP1_p2",,get_full_name());
      this.PUBReservedP1_p2.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_PUBReservedP1_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_PUBReservedP1_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMStartAddr_p2 extends uvm_reg;
	rand uvm_reg_field ACSMStartAddr_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMStartAddr_p2: coverpoint {m_data[10:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMStartAddr_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMStartAddr_p2 = uvm_reg_field::type_id::create("ACSMStartAddr_p2",,get_full_name());
      this.ACSMStartAddr_p2.configure(this, 11, 0, "RW", 0, 11'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMStartAddr_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMStartAddr_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMStopAddr_p2 extends uvm_reg;
	rand uvm_reg_field ACSMStopAddr_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMStopAddr_p2: coverpoint {m_data[10:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMStopAddr_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMStopAddr_p2 = uvm_reg_field::type_id::create("ACSMStopAddr_p2",,get_full_name());
      this.ACSMStopAddr_p2.configure(this, 11, 0, "RW", 0, 11'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMStopAddr_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMStopAddr_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRxEnPulse_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMRxEnPulse_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRxEnPulse_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRxEnPulse_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRxValPulse_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMRxValPulse_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRxValPulse_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRxValPulse_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMTxEnPulse_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMTxEnPulse_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMTxEnPulse_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMTxEnPulse_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWrcsPulse_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMWrcsPulse_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWrcsPulse_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWrcsPulse_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRdcsPulse_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMRdcsPulse_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRdcsPulse_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRdcsPulse_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteStaticLoPulse_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteStaticLoPulse_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteStaticLoPulse_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteStaticLoPulse_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteStaticHiPulse_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteStaticHiPulse_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteStaticHiPulse_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteStaticHiPulse_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteTogglePulse_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteTogglePulse_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteTogglePulse_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteTogglePulse_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteFastTogglePulse_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteFastTogglePulse_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteFastTogglePulse_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteFastTogglePulse_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckReadStaticLoPulse_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMWckReadStaticLoPulse_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckReadStaticLoPulse_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckReadStaticLoPulse_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckReadStaticHiPulse_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMWckReadStaticHiPulse_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckReadStaticHiPulse_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckReadStaticHiPulse_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckReadTogglePulse_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMWckReadTogglePulse_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckReadTogglePulse_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckReadTogglePulse_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckReadFastTogglePulse_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMWckReadFastTogglePulse_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckReadFastTogglePulse_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckReadFastTogglePulse_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwStaticLoPulse_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwStaticLoPulse_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwStaticLoPulse_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwStaticLoPulse_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwStaticHiPulse_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwStaticHiPulse_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwStaticHiPulse_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwStaticHiPulse_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwTogglePulse_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwTogglePulse_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwTogglePulse_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwTogglePulse_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwFastTogglePulse_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwFastTogglePulse_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwFastTogglePulse_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwFastTogglePulse_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreeRunMode_p2 extends uvm_reg;
	rand uvm_reg_field ACSMWckFreeRunMode_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMWckFreeRunMode_p2: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMWckFreeRunMode_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMWckFreeRunMode_p2 = uvm_reg_field::type_id::create("ACSMWckFreeRunMode_p2",,get_full_name());
      this.ACSMWckFreeRunMode_p2.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreeRunMode_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreeRunMode_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRptCntOverride_p2 extends uvm_reg;
	rand uvm_reg_field ACSMRptCntOverride_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMRptCntOverride_p2: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMRptCntOverride_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMRptCntOverride_p2 = uvm_reg_field::type_id::create("ACSMRptCntOverride_p2",,get_full_name());
      this.ACSMRptCntOverride_p2.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRptCntOverride_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRptCntOverride_p2


class ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRptCntDbl_p2 extends uvm_reg;
	rand uvm_reg_field ACSMRptCntDbl_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACSMRptCntDbl_p2: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_PPGC0_p2_ACSMRptCntDbl_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACSMRptCntDbl_p2 = uvm_reg_field::type_id::create("ACSMRptCntDbl_p2",,get_full_name());
      this.ACSMRptCntDbl_p2.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRptCntDbl_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRptCntDbl_p2


class ral_block_DWC_DDRPHYA_PPGC0_p2 extends uvm_reg_block;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiCustMode_p2 DfiCustMode_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_HwtMRL_p2 HwtMRL_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_PPTTrainSetup_p2 PPTTrainSetup_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_PhyMstrFreqOverride_p2 PhyMstrFreqOverride_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiHandshakeDelays0_p2 DfiHandshakeDelays0_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiRespHandshakeDelays0_p2 DfiRespHandshakeDelays0_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiHandshakeDelays1_p2 DfiHandshakeDelays1_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiRespHandshakeDelays1_p2 DfiRespHandshakeDelays1_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_PUBReservedP1_p2 PUBReservedP1_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMStartAddr_p2 ACSMStartAddr_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMStopAddr_p2 ACSMStopAddr_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRxEnPulse_p2 ACSMRxEnPulse_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRxValPulse_p2 ACSMRxValPulse_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMTxEnPulse_p2 ACSMTxEnPulse_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWrcsPulse_p2 ACSMWrcsPulse_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRdcsPulse_p2 ACSMRdcsPulse_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteStaticLoPulse_p2 ACSMWckWriteStaticLoPulse_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteStaticHiPulse_p2 ACSMWckWriteStaticHiPulse_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteTogglePulse_p2 ACSMWckWriteTogglePulse_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteFastTogglePulse_p2 ACSMWckWriteFastTogglePulse_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckReadStaticLoPulse_p2 ACSMWckReadStaticLoPulse_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckReadStaticHiPulse_p2 ACSMWckReadStaticHiPulse_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckReadTogglePulse_p2 ACSMWckReadTogglePulse_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckReadFastTogglePulse_p2 ACSMWckReadFastTogglePulse_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwStaticLoPulse_p2 ACSMWckFreqSwStaticLoPulse_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwStaticHiPulse_p2 ACSMWckFreqSwStaticHiPulse_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwTogglePulse_p2 ACSMWckFreqSwTogglePulse_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwFastTogglePulse_p2 ACSMWckFreqSwFastTogglePulse_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreeRunMode_p2 ACSMWckFreeRunMode_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRptCntOverride_p2 ACSMRptCntOverride_p2;
	rand ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRptCntDbl_p2 ACSMRptCntDbl_p2;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field DfiCustMode_p2_DfiCustMode_p2;
	rand uvm_reg_field HwtMRL_p2_HwtMRL_p2;
	rand uvm_reg_field PPTTrainSetup_p2_PhyMstrTrainInterval;
	rand uvm_reg_field PhyMstrTrainInterval;
	rand uvm_reg_field PPTTrainSetup_p2_PhyMstrMaxReqToAck;
	rand uvm_reg_field PhyMstrMaxReqToAck;
	rand uvm_reg_field PhyMstrFreqOverride_p2_PhyMstrFreqOverride_p2;
	rand uvm_reg_field DfiHandshakeDelays0_p2_PhyUpdAckDelay0;
	rand uvm_reg_field PhyUpdAckDelay0;
	rand uvm_reg_field DfiHandshakeDelays0_p2_PhyUpdReqDelay0;
	rand uvm_reg_field PhyUpdReqDelay0;
	rand uvm_reg_field DfiHandshakeDelays0_p2_CtrlUpdReqDelay0;
	rand uvm_reg_field CtrlUpdReqDelay0;
	rand uvm_reg_field DfiRespHandshakeDelays0_p2_LpCtrlAckDelay0;
	rand uvm_reg_field LpCtrlAckDelay0;
	rand uvm_reg_field DfiRespHandshakeDelays0_p2_LpDataAckDelay0;
	rand uvm_reg_field LpDataAckDelay0;
	rand uvm_reg_field DfiRespHandshakeDelays0_p2_CtrlUpdAckDelay0;
	rand uvm_reg_field CtrlUpdAckDelay0;
	rand uvm_reg_field DfiRespHandshakeDelays0_p2_LpAssertAckDelay0;
	rand uvm_reg_field LpAssertAckDelay0;
	rand uvm_reg_field DfiHandshakeDelays1_p2_PhyUpdAckDelay1;
	rand uvm_reg_field PhyUpdAckDelay1;
	rand uvm_reg_field DfiHandshakeDelays1_p2_PhyUpdReqDelay1;
	rand uvm_reg_field PhyUpdReqDelay1;
	rand uvm_reg_field DfiHandshakeDelays1_p2_CtrlUpdReqDelay1;
	rand uvm_reg_field CtrlUpdReqDelay1;
	rand uvm_reg_field DfiRespHandshakeDelays1_p2_LpCtrlAckDelay1;
	rand uvm_reg_field LpCtrlAckDelay1;
	rand uvm_reg_field DfiRespHandshakeDelays1_p2_LpDataAckDelay1;
	rand uvm_reg_field LpDataAckDelay1;
	rand uvm_reg_field DfiRespHandshakeDelays1_p2_CtrlUpdAckDelay1;
	rand uvm_reg_field CtrlUpdAckDelay1;
	rand uvm_reg_field DfiRespHandshakeDelays1_p2_LpAssertAckDelay1;
	rand uvm_reg_field LpAssertAckDelay1;
	rand uvm_reg_field PUBReservedP1_p2_PUBReservedP1_p2;
	rand uvm_reg_field ACSMStartAddr_p2_ACSMStartAddr_p2;
	rand uvm_reg_field ACSMStopAddr_p2_ACSMStopAddr_p2;
	rand uvm_reg_field ACSMRxEnPulse_p2_ACSMRxEnDelay;
	rand uvm_reg_field ACSMRxEnDelay;
	rand uvm_reg_field ACSMRxEnPulse_p2_ACSMRxEnDelayReserved;
	rand uvm_reg_field ACSMRxEnDelayReserved;
	rand uvm_reg_field ACSMRxEnPulse_p2_ACSMRxEnWidth;
	rand uvm_reg_field ACSMRxEnWidth;
	rand uvm_reg_field ACSMRxValPulse_p2_ACSMRxValDelay;
	rand uvm_reg_field ACSMRxValDelay;
	rand uvm_reg_field ACSMRxValPulse_p2_ACSMRxValDelayReserved;
	rand uvm_reg_field ACSMRxValDelayReserved;
	rand uvm_reg_field ACSMRxValPulse_p2_ACSMRxValWidth;
	rand uvm_reg_field ACSMRxValWidth;
	rand uvm_reg_field ACSMTxEnPulse_p2_ACSMTxEnDelay;
	rand uvm_reg_field ACSMTxEnDelay;
	rand uvm_reg_field ACSMTxEnPulse_p2_ACSMTxEnDelayReserved;
	rand uvm_reg_field ACSMTxEnDelayReserved;
	rand uvm_reg_field ACSMTxEnPulse_p2_ACSMTxEnWidth;
	rand uvm_reg_field ACSMTxEnWidth;
	rand uvm_reg_field ACSMWrcsPulse_p2_ACSMWrcsDelay;
	rand uvm_reg_field ACSMWrcsDelay;
	rand uvm_reg_field ACSMWrcsPulse_p2_ACSMWrcsDelayReserved;
	rand uvm_reg_field ACSMWrcsDelayReserved;
	rand uvm_reg_field ACSMWrcsPulse_p2_ACSMWrcsWidth;
	rand uvm_reg_field ACSMWrcsWidth;
	rand uvm_reg_field ACSMRdcsPulse_p2_ACSMRdcsDelay;
	rand uvm_reg_field ACSMRdcsDelay;
	rand uvm_reg_field ACSMRdcsPulse_p2_ACSMRdcsDelayReserved;
	rand uvm_reg_field ACSMRdcsDelayReserved;
	rand uvm_reg_field ACSMRdcsPulse_p2_ACSMRdcsWidth;
	rand uvm_reg_field ACSMRdcsWidth;
	rand uvm_reg_field ACSMWckWriteStaticLoPulse_p2_ACSMWckWriteStaticLoDelay;
	rand uvm_reg_field ACSMWckWriteStaticLoDelay;
	rand uvm_reg_field ACSMWckWriteStaticLoPulse_p2_ACSMWckWriteStaticLoDelayReserved;
	rand uvm_reg_field ACSMWckWriteStaticLoDelayReserved;
	rand uvm_reg_field ACSMWckWriteStaticLoPulse_p2_ACSMWckWriteStaticLoWidth;
	rand uvm_reg_field ACSMWckWriteStaticLoWidth;
	rand uvm_reg_field ACSMWckWriteStaticHiPulse_p2_ACSMWckWriteStaticHiDelay;
	rand uvm_reg_field ACSMWckWriteStaticHiDelay;
	rand uvm_reg_field ACSMWckWriteStaticHiPulse_p2_ACSMWckWriteStaticHiDelayReserved;
	rand uvm_reg_field ACSMWckWriteStaticHiDelayReserved;
	rand uvm_reg_field ACSMWckWriteStaticHiPulse_p2_ACSMWckWriteStaticHiWidth;
	rand uvm_reg_field ACSMWckWriteStaticHiWidth;
	rand uvm_reg_field ACSMWckWriteTogglePulse_p2_ACSMWckWriteToggleDelay;
	rand uvm_reg_field ACSMWckWriteToggleDelay;
	rand uvm_reg_field ACSMWckWriteTogglePulse_p2_ACSMWckWriteToggleDelayReserved;
	rand uvm_reg_field ACSMWckWriteToggleDelayReserved;
	rand uvm_reg_field ACSMWckWriteTogglePulse_p2_ACSMWckWriteToggleWidth;
	rand uvm_reg_field ACSMWckWriteToggleWidth;
	rand uvm_reg_field ACSMWckWriteFastTogglePulse_p2_ACSMWckWriteFastToggleDelay;
	rand uvm_reg_field ACSMWckWriteFastToggleDelay;
	rand uvm_reg_field ACSMWckWriteFastTogglePulse_p2_ACSMWckWriteFastToggleDelayReserved;
	rand uvm_reg_field ACSMWckWriteFastToggleDelayReserved;
	rand uvm_reg_field ACSMWckWriteFastTogglePulse_p2_ACSMWckWriteFastToggleWidth;
	rand uvm_reg_field ACSMWckWriteFastToggleWidth;
	rand uvm_reg_field ACSMWckReadStaticLoPulse_p2_ACSMWckReadStaticLoDelay;
	rand uvm_reg_field ACSMWckReadStaticLoDelay;
	rand uvm_reg_field ACSMWckReadStaticLoPulse_p2_ACSMWckReadStaticLoDelayReserved;
	rand uvm_reg_field ACSMWckReadStaticLoDelayReserved;
	rand uvm_reg_field ACSMWckReadStaticLoPulse_p2_ACSMWckReadStaticLoWidth;
	rand uvm_reg_field ACSMWckReadStaticLoWidth;
	rand uvm_reg_field ACSMWckReadStaticHiPulse_p2_ACSMWckReadStaticHiDelay;
	rand uvm_reg_field ACSMWckReadStaticHiDelay;
	rand uvm_reg_field ACSMWckReadStaticHiPulse_p2_ACSMWckReadStaticHiDelayReserved;
	rand uvm_reg_field ACSMWckReadStaticHiDelayReserved;
	rand uvm_reg_field ACSMWckReadStaticHiPulse_p2_ACSMWckReadStaticHiWidth;
	rand uvm_reg_field ACSMWckReadStaticHiWidth;
	rand uvm_reg_field ACSMWckReadTogglePulse_p2_ACSMWckReadToggleDelay;
	rand uvm_reg_field ACSMWckReadToggleDelay;
	rand uvm_reg_field ACSMWckReadTogglePulse_p2_ACSMWckReadToggleDelayReserved;
	rand uvm_reg_field ACSMWckReadToggleDelayReserved;
	rand uvm_reg_field ACSMWckReadTogglePulse_p2_ACSMWckReadToggleWidth;
	rand uvm_reg_field ACSMWckReadToggleWidth;
	rand uvm_reg_field ACSMWckReadFastTogglePulse_p2_ACSMWckReadFastToggleDelay;
	rand uvm_reg_field ACSMWckReadFastToggleDelay;
	rand uvm_reg_field ACSMWckReadFastTogglePulse_p2_ACSMWckReadFastToggleDelayReserved;
	rand uvm_reg_field ACSMWckReadFastToggleDelayReserved;
	rand uvm_reg_field ACSMWckReadFastTogglePulse_p2_ACSMWckReadFastToggleWidth;
	rand uvm_reg_field ACSMWckReadFastToggleWidth;
	rand uvm_reg_field ACSMWckFreqSwStaticLoPulse_p2_ACSMWckFreqSwStaticLoDelay;
	rand uvm_reg_field ACSMWckFreqSwStaticLoDelay;
	rand uvm_reg_field ACSMWckFreqSwStaticLoPulse_p2_ACSMWckFreqSwStaticLoDelayReserved;
	rand uvm_reg_field ACSMWckFreqSwStaticLoDelayReserved;
	rand uvm_reg_field ACSMWckFreqSwStaticLoPulse_p2_ACSMWckFreqSwStaticLoWidth;
	rand uvm_reg_field ACSMWckFreqSwStaticLoWidth;
	rand uvm_reg_field ACSMWckFreqSwStaticHiPulse_p2_ACSMWckFreqSwStaticHiDelay;
	rand uvm_reg_field ACSMWckFreqSwStaticHiDelay;
	rand uvm_reg_field ACSMWckFreqSwStaticHiPulse_p2_ACSMWckFreqSwStaticHiDelayReserved;
	rand uvm_reg_field ACSMWckFreqSwStaticHiDelayReserved;
	rand uvm_reg_field ACSMWckFreqSwStaticHiPulse_p2_ACSMWckFreqSwStaticHiWidth;
	rand uvm_reg_field ACSMWckFreqSwStaticHiWidth;
	rand uvm_reg_field ACSMWckFreqSwTogglePulse_p2_ACSMWckFreqSwToggleDelay;
	rand uvm_reg_field ACSMWckFreqSwToggleDelay;
	rand uvm_reg_field ACSMWckFreqSwTogglePulse_p2_ACSMWckFreqSwToggleDelayReserved;
	rand uvm_reg_field ACSMWckFreqSwToggleDelayReserved;
	rand uvm_reg_field ACSMWckFreqSwTogglePulse_p2_ACSMWckFreqSwToggleWidth;
	rand uvm_reg_field ACSMWckFreqSwToggleWidth;
	rand uvm_reg_field ACSMWckFreqSwFastTogglePulse_p2_ACSMWckFreqSwFastToggleDelay;
	rand uvm_reg_field ACSMWckFreqSwFastToggleDelay;
	rand uvm_reg_field ACSMWckFreqSwFastTogglePulse_p2_ACSMWckFreqSwFastToggleDelayReserved;
	rand uvm_reg_field ACSMWckFreqSwFastToggleDelayReserved;
	rand uvm_reg_field ACSMWckFreqSwFastTogglePulse_p2_ACSMWckFreqSwFastToggleWidth;
	rand uvm_reg_field ACSMWckFreqSwFastToggleWidth;
	rand uvm_reg_field ACSMWckFreeRunMode_p2_ACSMWckFreeRunMode_p2;
	rand uvm_reg_field ACSMRptCntOverride_p2_ACSMRptCntOverride_p2;
	rand uvm_reg_field ACSMRptCntDbl_p2_ACSMRptCntDbl_p2;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	DfiCustMode_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB };
		option.weight = 1;
	}

	HwtMRL_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD };
		option.weight = 1;
	}

	PPTTrainSetup_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h40 };
		option.weight = 1;
	}

	PhyMstrFreqOverride_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h41 };
		option.weight = 1;
	}

	DfiHandshakeDelays0_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h66 };
		option.weight = 1;
	}

	DfiRespHandshakeDelays0_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h6B };
		option.weight = 1;
	}

	DfiHandshakeDelays1_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hE6 };
		option.weight = 1;
	}

	DfiRespHandshakeDelays1_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hEB };
		option.weight = 1;
	}

	PUBReservedP1_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFF };
		option.weight = 1;
	}

	ACSMStartAddr_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h122 };
		option.weight = 1;
	}

	ACSMStopAddr_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h123 };
		option.weight = 1;
	}

	ACSMRxEnPulse_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h12C };
		option.weight = 1;
	}

	ACSMRxValPulse_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h12D };
		option.weight = 1;
	}

	ACSMTxEnPulse_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h12E };
		option.weight = 1;
	}

	ACSMWrcsPulse_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h12F };
		option.weight = 1;
	}

	ACSMRdcsPulse_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h130 };
		option.weight = 1;
	}

	ACSMWckWriteStaticLoPulse_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h135 };
		option.weight = 1;
	}

	ACSMWckWriteStaticHiPulse_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h136 };
		option.weight = 1;
	}

	ACSMWckWriteTogglePulse_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h137 };
		option.weight = 1;
	}

	ACSMWckWriteFastTogglePulse_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h138 };
		option.weight = 1;
	}

	ACSMWckReadStaticLoPulse_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h139 };
		option.weight = 1;
	}

	ACSMWckReadStaticHiPulse_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h13A };
		option.weight = 1;
	}

	ACSMWckReadTogglePulse_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h13B };
		option.weight = 1;
	}

	ACSMWckReadFastTogglePulse_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h13C };
		option.weight = 1;
	}

	ACSMWckFreqSwStaticLoPulse_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h13D };
		option.weight = 1;
	}

	ACSMWckFreqSwStaticHiPulse_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h13E };
		option.weight = 1;
	}

	ACSMWckFreqSwTogglePulse_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h13F };
		option.weight = 1;
	}

	ACSMWckFreqSwFastTogglePulse_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h140 };
		option.weight = 1;
	}

	ACSMWckFreeRunMode_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h141 };
		option.weight = 1;
	}

	ACSMRptCntOverride_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h145 };
		option.weight = 1;
	}

	ACSMRptCntDbl_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h146 };
		option.weight = 1;
	}
endgroup
	function new(string name = "DWC_DDRPHYA_PPGC0_p2");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.DfiCustMode_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiCustMode_p2::type_id::create("DfiCustMode_p2",,get_full_name());
      if(this.DfiCustMode_p2.has_coverage(UVM_CVR_ALL))
      	this.DfiCustMode_p2.cg_bits.option.name = {get_name(), ".", "DfiCustMode_p2_bits"};
      this.DfiCustMode_p2.configure(this, null, "");
      this.DfiCustMode_p2.build();
      this.default_map.add_reg(this.DfiCustMode_p2, `UVM_REG_ADDR_WIDTH'hB, "RW", 0);
		this.DfiCustMode_p2_DfiCustMode_p2 = this.DfiCustMode_p2.DfiCustMode_p2;
      this.HwtMRL_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_HwtMRL_p2::type_id::create("HwtMRL_p2",,get_full_name());
      if(this.HwtMRL_p2.has_coverage(UVM_CVR_ALL))
      	this.HwtMRL_p2.cg_bits.option.name = {get_name(), ".", "HwtMRL_p2_bits"};
      this.HwtMRL_p2.configure(this, null, "");
      this.HwtMRL_p2.build();
      this.default_map.add_reg(this.HwtMRL_p2, `UVM_REG_ADDR_WIDTH'hD, "RW", 0);
		this.HwtMRL_p2_HwtMRL_p2 = this.HwtMRL_p2.HwtMRL_p2;
      this.PPTTrainSetup_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_PPTTrainSetup_p2::type_id::create("PPTTrainSetup_p2",,get_full_name());
      if(this.PPTTrainSetup_p2.has_coverage(UVM_CVR_ALL))
      	this.PPTTrainSetup_p2.cg_bits.option.name = {get_name(), ".", "PPTTrainSetup_p2_bits"};
      this.PPTTrainSetup_p2.configure(this, null, "");
      this.PPTTrainSetup_p2.build();
      this.default_map.add_reg(this.PPTTrainSetup_p2, `UVM_REG_ADDR_WIDTH'h40, "RW", 0);
		this.PPTTrainSetup_p2_PhyMstrTrainInterval = this.PPTTrainSetup_p2.PhyMstrTrainInterval;
		this.PhyMstrTrainInterval = this.PPTTrainSetup_p2.PhyMstrTrainInterval;
		this.PPTTrainSetup_p2_PhyMstrMaxReqToAck = this.PPTTrainSetup_p2.PhyMstrMaxReqToAck;
		this.PhyMstrMaxReqToAck = this.PPTTrainSetup_p2.PhyMstrMaxReqToAck;
      this.PhyMstrFreqOverride_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_PhyMstrFreqOverride_p2::type_id::create("PhyMstrFreqOverride_p2",,get_full_name());
      if(this.PhyMstrFreqOverride_p2.has_coverage(UVM_CVR_ALL))
      	this.PhyMstrFreqOverride_p2.cg_bits.option.name = {get_name(), ".", "PhyMstrFreqOverride_p2_bits"};
      this.PhyMstrFreqOverride_p2.configure(this, null, "");
      this.PhyMstrFreqOverride_p2.build();
      this.default_map.add_reg(this.PhyMstrFreqOverride_p2, `UVM_REG_ADDR_WIDTH'h41, "RW", 0);
		this.PhyMstrFreqOverride_p2_PhyMstrFreqOverride_p2 = this.PhyMstrFreqOverride_p2.PhyMstrFreqOverride_p2;
      this.DfiHandshakeDelays0_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiHandshakeDelays0_p2::type_id::create("DfiHandshakeDelays0_p2",,get_full_name());
      if(this.DfiHandshakeDelays0_p2.has_coverage(UVM_CVR_ALL))
      	this.DfiHandshakeDelays0_p2.cg_bits.option.name = {get_name(), ".", "DfiHandshakeDelays0_p2_bits"};
      this.DfiHandshakeDelays0_p2.configure(this, null, "");
      this.DfiHandshakeDelays0_p2.build();
      this.default_map.add_reg(this.DfiHandshakeDelays0_p2, `UVM_REG_ADDR_WIDTH'h66, "RW", 0);
		this.DfiHandshakeDelays0_p2_PhyUpdAckDelay0 = this.DfiHandshakeDelays0_p2.PhyUpdAckDelay0;
		this.PhyUpdAckDelay0 = this.DfiHandshakeDelays0_p2.PhyUpdAckDelay0;
		this.DfiHandshakeDelays0_p2_PhyUpdReqDelay0 = this.DfiHandshakeDelays0_p2.PhyUpdReqDelay0;
		this.PhyUpdReqDelay0 = this.DfiHandshakeDelays0_p2.PhyUpdReqDelay0;
		this.DfiHandshakeDelays0_p2_CtrlUpdReqDelay0 = this.DfiHandshakeDelays0_p2.CtrlUpdReqDelay0;
		this.CtrlUpdReqDelay0 = this.DfiHandshakeDelays0_p2.CtrlUpdReqDelay0;
      this.DfiRespHandshakeDelays0_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiRespHandshakeDelays0_p2::type_id::create("DfiRespHandshakeDelays0_p2",,get_full_name());
      if(this.DfiRespHandshakeDelays0_p2.has_coverage(UVM_CVR_ALL))
      	this.DfiRespHandshakeDelays0_p2.cg_bits.option.name = {get_name(), ".", "DfiRespHandshakeDelays0_p2_bits"};
      this.DfiRespHandshakeDelays0_p2.configure(this, null, "");
      this.DfiRespHandshakeDelays0_p2.build();
      this.default_map.add_reg(this.DfiRespHandshakeDelays0_p2, `UVM_REG_ADDR_WIDTH'h6B, "RW", 0);
		this.DfiRespHandshakeDelays0_p2_LpCtrlAckDelay0 = this.DfiRespHandshakeDelays0_p2.LpCtrlAckDelay0;
		this.LpCtrlAckDelay0 = this.DfiRespHandshakeDelays0_p2.LpCtrlAckDelay0;
		this.DfiRespHandshakeDelays0_p2_LpDataAckDelay0 = this.DfiRespHandshakeDelays0_p2.LpDataAckDelay0;
		this.LpDataAckDelay0 = this.DfiRespHandshakeDelays0_p2.LpDataAckDelay0;
		this.DfiRespHandshakeDelays0_p2_CtrlUpdAckDelay0 = this.DfiRespHandshakeDelays0_p2.CtrlUpdAckDelay0;
		this.CtrlUpdAckDelay0 = this.DfiRespHandshakeDelays0_p2.CtrlUpdAckDelay0;
		this.DfiRespHandshakeDelays0_p2_LpAssertAckDelay0 = this.DfiRespHandshakeDelays0_p2.LpAssertAckDelay0;
		this.LpAssertAckDelay0 = this.DfiRespHandshakeDelays0_p2.LpAssertAckDelay0;
      this.DfiHandshakeDelays1_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiHandshakeDelays1_p2::type_id::create("DfiHandshakeDelays1_p2",,get_full_name());
      if(this.DfiHandshakeDelays1_p2.has_coverage(UVM_CVR_ALL))
      	this.DfiHandshakeDelays1_p2.cg_bits.option.name = {get_name(), ".", "DfiHandshakeDelays1_p2_bits"};
      this.DfiHandshakeDelays1_p2.configure(this, null, "");
      this.DfiHandshakeDelays1_p2.build();
      this.default_map.add_reg(this.DfiHandshakeDelays1_p2, `UVM_REG_ADDR_WIDTH'hE6, "RW", 0);
		this.DfiHandshakeDelays1_p2_PhyUpdAckDelay1 = this.DfiHandshakeDelays1_p2.PhyUpdAckDelay1;
		this.PhyUpdAckDelay1 = this.DfiHandshakeDelays1_p2.PhyUpdAckDelay1;
		this.DfiHandshakeDelays1_p2_PhyUpdReqDelay1 = this.DfiHandshakeDelays1_p2.PhyUpdReqDelay1;
		this.PhyUpdReqDelay1 = this.DfiHandshakeDelays1_p2.PhyUpdReqDelay1;
		this.DfiHandshakeDelays1_p2_CtrlUpdReqDelay1 = this.DfiHandshakeDelays1_p2.CtrlUpdReqDelay1;
		this.CtrlUpdReqDelay1 = this.DfiHandshakeDelays1_p2.CtrlUpdReqDelay1;
      this.DfiRespHandshakeDelays1_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_DfiRespHandshakeDelays1_p2::type_id::create("DfiRespHandshakeDelays1_p2",,get_full_name());
      if(this.DfiRespHandshakeDelays1_p2.has_coverage(UVM_CVR_ALL))
      	this.DfiRespHandshakeDelays1_p2.cg_bits.option.name = {get_name(), ".", "DfiRespHandshakeDelays1_p2_bits"};
      this.DfiRespHandshakeDelays1_p2.configure(this, null, "");
      this.DfiRespHandshakeDelays1_p2.build();
      this.default_map.add_reg(this.DfiRespHandshakeDelays1_p2, `UVM_REG_ADDR_WIDTH'hEB, "RW", 0);
		this.DfiRespHandshakeDelays1_p2_LpCtrlAckDelay1 = this.DfiRespHandshakeDelays1_p2.LpCtrlAckDelay1;
		this.LpCtrlAckDelay1 = this.DfiRespHandshakeDelays1_p2.LpCtrlAckDelay1;
		this.DfiRespHandshakeDelays1_p2_LpDataAckDelay1 = this.DfiRespHandshakeDelays1_p2.LpDataAckDelay1;
		this.LpDataAckDelay1 = this.DfiRespHandshakeDelays1_p2.LpDataAckDelay1;
		this.DfiRespHandshakeDelays1_p2_CtrlUpdAckDelay1 = this.DfiRespHandshakeDelays1_p2.CtrlUpdAckDelay1;
		this.CtrlUpdAckDelay1 = this.DfiRespHandshakeDelays1_p2.CtrlUpdAckDelay1;
		this.DfiRespHandshakeDelays1_p2_LpAssertAckDelay1 = this.DfiRespHandshakeDelays1_p2.LpAssertAckDelay1;
		this.LpAssertAckDelay1 = this.DfiRespHandshakeDelays1_p2.LpAssertAckDelay1;
      this.PUBReservedP1_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_PUBReservedP1_p2::type_id::create("PUBReservedP1_p2",,get_full_name());
      if(this.PUBReservedP1_p2.has_coverage(UVM_CVR_ALL))
      	this.PUBReservedP1_p2.cg_bits.option.name = {get_name(), ".", "PUBReservedP1_p2_bits"};
      this.PUBReservedP1_p2.configure(this, null, "");
      this.PUBReservedP1_p2.build();
      this.default_map.add_reg(this.PUBReservedP1_p2, `UVM_REG_ADDR_WIDTH'hFF, "RW", 0);
		this.PUBReservedP1_p2_PUBReservedP1_p2 = this.PUBReservedP1_p2.PUBReservedP1_p2;
      this.ACSMStartAddr_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMStartAddr_p2::type_id::create("ACSMStartAddr_p2",,get_full_name());
      if(this.ACSMStartAddr_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMStartAddr_p2.cg_bits.option.name = {get_name(), ".", "ACSMStartAddr_p2_bits"};
      this.ACSMStartAddr_p2.configure(this, null, "");
      this.ACSMStartAddr_p2.build();
      this.default_map.add_reg(this.ACSMStartAddr_p2, `UVM_REG_ADDR_WIDTH'h122, "RW", 0);
		this.ACSMStartAddr_p2_ACSMStartAddr_p2 = this.ACSMStartAddr_p2.ACSMStartAddr_p2;
      this.ACSMStopAddr_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMStopAddr_p2::type_id::create("ACSMStopAddr_p2",,get_full_name());
      if(this.ACSMStopAddr_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMStopAddr_p2.cg_bits.option.name = {get_name(), ".", "ACSMStopAddr_p2_bits"};
      this.ACSMStopAddr_p2.configure(this, null, "");
      this.ACSMStopAddr_p2.build();
      this.default_map.add_reg(this.ACSMStopAddr_p2, `UVM_REG_ADDR_WIDTH'h123, "RW", 0);
		this.ACSMStopAddr_p2_ACSMStopAddr_p2 = this.ACSMStopAddr_p2.ACSMStopAddr_p2;
      this.ACSMRxEnPulse_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRxEnPulse_p2::type_id::create("ACSMRxEnPulse_p2",,get_full_name());
      if(this.ACSMRxEnPulse_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMRxEnPulse_p2.cg_bits.option.name = {get_name(), ".", "ACSMRxEnPulse_p2_bits"};
      this.ACSMRxEnPulse_p2.configure(this, null, "");
      this.ACSMRxEnPulse_p2.build();
      this.default_map.add_reg(this.ACSMRxEnPulse_p2, `UVM_REG_ADDR_WIDTH'h12C, "RW", 0);
		this.ACSMRxEnPulse_p2_ACSMRxEnDelay = this.ACSMRxEnPulse_p2.ACSMRxEnDelay;
		this.ACSMRxEnDelay = this.ACSMRxEnPulse_p2.ACSMRxEnDelay;
		this.ACSMRxEnPulse_p2_ACSMRxEnDelayReserved = this.ACSMRxEnPulse_p2.ACSMRxEnDelayReserved;
		this.ACSMRxEnDelayReserved = this.ACSMRxEnPulse_p2.ACSMRxEnDelayReserved;
		this.ACSMRxEnPulse_p2_ACSMRxEnWidth = this.ACSMRxEnPulse_p2.ACSMRxEnWidth;
		this.ACSMRxEnWidth = this.ACSMRxEnPulse_p2.ACSMRxEnWidth;
      this.ACSMRxValPulse_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRxValPulse_p2::type_id::create("ACSMRxValPulse_p2",,get_full_name());
      if(this.ACSMRxValPulse_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMRxValPulse_p2.cg_bits.option.name = {get_name(), ".", "ACSMRxValPulse_p2_bits"};
      this.ACSMRxValPulse_p2.configure(this, null, "");
      this.ACSMRxValPulse_p2.build();
      this.default_map.add_reg(this.ACSMRxValPulse_p2, `UVM_REG_ADDR_WIDTH'h12D, "RW", 0);
		this.ACSMRxValPulse_p2_ACSMRxValDelay = this.ACSMRxValPulse_p2.ACSMRxValDelay;
		this.ACSMRxValDelay = this.ACSMRxValPulse_p2.ACSMRxValDelay;
		this.ACSMRxValPulse_p2_ACSMRxValDelayReserved = this.ACSMRxValPulse_p2.ACSMRxValDelayReserved;
		this.ACSMRxValDelayReserved = this.ACSMRxValPulse_p2.ACSMRxValDelayReserved;
		this.ACSMRxValPulse_p2_ACSMRxValWidth = this.ACSMRxValPulse_p2.ACSMRxValWidth;
		this.ACSMRxValWidth = this.ACSMRxValPulse_p2.ACSMRxValWidth;
      this.ACSMTxEnPulse_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMTxEnPulse_p2::type_id::create("ACSMTxEnPulse_p2",,get_full_name());
      if(this.ACSMTxEnPulse_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMTxEnPulse_p2.cg_bits.option.name = {get_name(), ".", "ACSMTxEnPulse_p2_bits"};
      this.ACSMTxEnPulse_p2.configure(this, null, "");
      this.ACSMTxEnPulse_p2.build();
      this.default_map.add_reg(this.ACSMTxEnPulse_p2, `UVM_REG_ADDR_WIDTH'h12E, "RW", 0);
		this.ACSMTxEnPulse_p2_ACSMTxEnDelay = this.ACSMTxEnPulse_p2.ACSMTxEnDelay;
		this.ACSMTxEnDelay = this.ACSMTxEnPulse_p2.ACSMTxEnDelay;
		this.ACSMTxEnPulse_p2_ACSMTxEnDelayReserved = this.ACSMTxEnPulse_p2.ACSMTxEnDelayReserved;
		this.ACSMTxEnDelayReserved = this.ACSMTxEnPulse_p2.ACSMTxEnDelayReserved;
		this.ACSMTxEnPulse_p2_ACSMTxEnWidth = this.ACSMTxEnPulse_p2.ACSMTxEnWidth;
		this.ACSMTxEnWidth = this.ACSMTxEnPulse_p2.ACSMTxEnWidth;
      this.ACSMWrcsPulse_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWrcsPulse_p2::type_id::create("ACSMWrcsPulse_p2",,get_full_name());
      if(this.ACSMWrcsPulse_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMWrcsPulse_p2.cg_bits.option.name = {get_name(), ".", "ACSMWrcsPulse_p2_bits"};
      this.ACSMWrcsPulse_p2.configure(this, null, "");
      this.ACSMWrcsPulse_p2.build();
      this.default_map.add_reg(this.ACSMWrcsPulse_p2, `UVM_REG_ADDR_WIDTH'h12F, "RW", 0);
		this.ACSMWrcsPulse_p2_ACSMWrcsDelay = this.ACSMWrcsPulse_p2.ACSMWrcsDelay;
		this.ACSMWrcsDelay = this.ACSMWrcsPulse_p2.ACSMWrcsDelay;
		this.ACSMWrcsPulse_p2_ACSMWrcsDelayReserved = this.ACSMWrcsPulse_p2.ACSMWrcsDelayReserved;
		this.ACSMWrcsDelayReserved = this.ACSMWrcsPulse_p2.ACSMWrcsDelayReserved;
		this.ACSMWrcsPulse_p2_ACSMWrcsWidth = this.ACSMWrcsPulse_p2.ACSMWrcsWidth;
		this.ACSMWrcsWidth = this.ACSMWrcsPulse_p2.ACSMWrcsWidth;
      this.ACSMRdcsPulse_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRdcsPulse_p2::type_id::create("ACSMRdcsPulse_p2",,get_full_name());
      if(this.ACSMRdcsPulse_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMRdcsPulse_p2.cg_bits.option.name = {get_name(), ".", "ACSMRdcsPulse_p2_bits"};
      this.ACSMRdcsPulse_p2.configure(this, null, "");
      this.ACSMRdcsPulse_p2.build();
      this.default_map.add_reg(this.ACSMRdcsPulse_p2, `UVM_REG_ADDR_WIDTH'h130, "RW", 0);
		this.ACSMRdcsPulse_p2_ACSMRdcsDelay = this.ACSMRdcsPulse_p2.ACSMRdcsDelay;
		this.ACSMRdcsDelay = this.ACSMRdcsPulse_p2.ACSMRdcsDelay;
		this.ACSMRdcsPulse_p2_ACSMRdcsDelayReserved = this.ACSMRdcsPulse_p2.ACSMRdcsDelayReserved;
		this.ACSMRdcsDelayReserved = this.ACSMRdcsPulse_p2.ACSMRdcsDelayReserved;
		this.ACSMRdcsPulse_p2_ACSMRdcsWidth = this.ACSMRdcsPulse_p2.ACSMRdcsWidth;
		this.ACSMRdcsWidth = this.ACSMRdcsPulse_p2.ACSMRdcsWidth;
      this.ACSMWckWriteStaticLoPulse_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteStaticLoPulse_p2::type_id::create("ACSMWckWriteStaticLoPulse_p2",,get_full_name());
      if(this.ACSMWckWriteStaticLoPulse_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckWriteStaticLoPulse_p2.cg_bits.option.name = {get_name(), ".", "ACSMWckWriteStaticLoPulse_p2_bits"};
      this.ACSMWckWriteStaticLoPulse_p2.configure(this, null, "");
      this.ACSMWckWriteStaticLoPulse_p2.build();
      this.default_map.add_reg(this.ACSMWckWriteStaticLoPulse_p2, `UVM_REG_ADDR_WIDTH'h135, "RW", 0);
		this.ACSMWckWriteStaticLoPulse_p2_ACSMWckWriteStaticLoDelay = this.ACSMWckWriteStaticLoPulse_p2.ACSMWckWriteStaticLoDelay;
		this.ACSMWckWriteStaticLoDelay = this.ACSMWckWriteStaticLoPulse_p2.ACSMWckWriteStaticLoDelay;
		this.ACSMWckWriteStaticLoPulse_p2_ACSMWckWriteStaticLoDelayReserved = this.ACSMWckWriteStaticLoPulse_p2.ACSMWckWriteStaticLoDelayReserved;
		this.ACSMWckWriteStaticLoDelayReserved = this.ACSMWckWriteStaticLoPulse_p2.ACSMWckWriteStaticLoDelayReserved;
		this.ACSMWckWriteStaticLoPulse_p2_ACSMWckWriteStaticLoWidth = this.ACSMWckWriteStaticLoPulse_p2.ACSMWckWriteStaticLoWidth;
		this.ACSMWckWriteStaticLoWidth = this.ACSMWckWriteStaticLoPulse_p2.ACSMWckWriteStaticLoWidth;
      this.ACSMWckWriteStaticHiPulse_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteStaticHiPulse_p2::type_id::create("ACSMWckWriteStaticHiPulse_p2",,get_full_name());
      if(this.ACSMWckWriteStaticHiPulse_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckWriteStaticHiPulse_p2.cg_bits.option.name = {get_name(), ".", "ACSMWckWriteStaticHiPulse_p2_bits"};
      this.ACSMWckWriteStaticHiPulse_p2.configure(this, null, "");
      this.ACSMWckWriteStaticHiPulse_p2.build();
      this.default_map.add_reg(this.ACSMWckWriteStaticHiPulse_p2, `UVM_REG_ADDR_WIDTH'h136, "RW", 0);
		this.ACSMWckWriteStaticHiPulse_p2_ACSMWckWriteStaticHiDelay = this.ACSMWckWriteStaticHiPulse_p2.ACSMWckWriteStaticHiDelay;
		this.ACSMWckWriteStaticHiDelay = this.ACSMWckWriteStaticHiPulse_p2.ACSMWckWriteStaticHiDelay;
		this.ACSMWckWriteStaticHiPulse_p2_ACSMWckWriteStaticHiDelayReserved = this.ACSMWckWriteStaticHiPulse_p2.ACSMWckWriteStaticHiDelayReserved;
		this.ACSMWckWriteStaticHiDelayReserved = this.ACSMWckWriteStaticHiPulse_p2.ACSMWckWriteStaticHiDelayReserved;
		this.ACSMWckWriteStaticHiPulse_p2_ACSMWckWriteStaticHiWidth = this.ACSMWckWriteStaticHiPulse_p2.ACSMWckWriteStaticHiWidth;
		this.ACSMWckWriteStaticHiWidth = this.ACSMWckWriteStaticHiPulse_p2.ACSMWckWriteStaticHiWidth;
      this.ACSMWckWriteTogglePulse_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteTogglePulse_p2::type_id::create("ACSMWckWriteTogglePulse_p2",,get_full_name());
      if(this.ACSMWckWriteTogglePulse_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckWriteTogglePulse_p2.cg_bits.option.name = {get_name(), ".", "ACSMWckWriteTogglePulse_p2_bits"};
      this.ACSMWckWriteTogglePulse_p2.configure(this, null, "");
      this.ACSMWckWriteTogglePulse_p2.build();
      this.default_map.add_reg(this.ACSMWckWriteTogglePulse_p2, `UVM_REG_ADDR_WIDTH'h137, "RW", 0);
		this.ACSMWckWriteTogglePulse_p2_ACSMWckWriteToggleDelay = this.ACSMWckWriteTogglePulse_p2.ACSMWckWriteToggleDelay;
		this.ACSMWckWriteToggleDelay = this.ACSMWckWriteTogglePulse_p2.ACSMWckWriteToggleDelay;
		this.ACSMWckWriteTogglePulse_p2_ACSMWckWriteToggleDelayReserved = this.ACSMWckWriteTogglePulse_p2.ACSMWckWriteToggleDelayReserved;
		this.ACSMWckWriteToggleDelayReserved = this.ACSMWckWriteTogglePulse_p2.ACSMWckWriteToggleDelayReserved;
		this.ACSMWckWriteTogglePulse_p2_ACSMWckWriteToggleWidth = this.ACSMWckWriteTogglePulse_p2.ACSMWckWriteToggleWidth;
		this.ACSMWckWriteToggleWidth = this.ACSMWckWriteTogglePulse_p2.ACSMWckWriteToggleWidth;
      this.ACSMWckWriteFastTogglePulse_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckWriteFastTogglePulse_p2::type_id::create("ACSMWckWriteFastTogglePulse_p2",,get_full_name());
      if(this.ACSMWckWriteFastTogglePulse_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckWriteFastTogglePulse_p2.cg_bits.option.name = {get_name(), ".", "ACSMWckWriteFastTogglePulse_p2_bits"};
      this.ACSMWckWriteFastTogglePulse_p2.configure(this, null, "");
      this.ACSMWckWriteFastTogglePulse_p2.build();
      this.default_map.add_reg(this.ACSMWckWriteFastTogglePulse_p2, `UVM_REG_ADDR_WIDTH'h138, "RW", 0);
		this.ACSMWckWriteFastTogglePulse_p2_ACSMWckWriteFastToggleDelay = this.ACSMWckWriteFastTogglePulse_p2.ACSMWckWriteFastToggleDelay;
		this.ACSMWckWriteFastToggleDelay = this.ACSMWckWriteFastTogglePulse_p2.ACSMWckWriteFastToggleDelay;
		this.ACSMWckWriteFastTogglePulse_p2_ACSMWckWriteFastToggleDelayReserved = this.ACSMWckWriteFastTogglePulse_p2.ACSMWckWriteFastToggleDelayReserved;
		this.ACSMWckWriteFastToggleDelayReserved = this.ACSMWckWriteFastTogglePulse_p2.ACSMWckWriteFastToggleDelayReserved;
		this.ACSMWckWriteFastTogglePulse_p2_ACSMWckWriteFastToggleWidth = this.ACSMWckWriteFastTogglePulse_p2.ACSMWckWriteFastToggleWidth;
		this.ACSMWckWriteFastToggleWidth = this.ACSMWckWriteFastTogglePulse_p2.ACSMWckWriteFastToggleWidth;
      this.ACSMWckReadStaticLoPulse_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckReadStaticLoPulse_p2::type_id::create("ACSMWckReadStaticLoPulse_p2",,get_full_name());
      if(this.ACSMWckReadStaticLoPulse_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckReadStaticLoPulse_p2.cg_bits.option.name = {get_name(), ".", "ACSMWckReadStaticLoPulse_p2_bits"};
      this.ACSMWckReadStaticLoPulse_p2.configure(this, null, "");
      this.ACSMWckReadStaticLoPulse_p2.build();
      this.default_map.add_reg(this.ACSMWckReadStaticLoPulse_p2, `UVM_REG_ADDR_WIDTH'h139, "RW", 0);
		this.ACSMWckReadStaticLoPulse_p2_ACSMWckReadStaticLoDelay = this.ACSMWckReadStaticLoPulse_p2.ACSMWckReadStaticLoDelay;
		this.ACSMWckReadStaticLoDelay = this.ACSMWckReadStaticLoPulse_p2.ACSMWckReadStaticLoDelay;
		this.ACSMWckReadStaticLoPulse_p2_ACSMWckReadStaticLoDelayReserved = this.ACSMWckReadStaticLoPulse_p2.ACSMWckReadStaticLoDelayReserved;
		this.ACSMWckReadStaticLoDelayReserved = this.ACSMWckReadStaticLoPulse_p2.ACSMWckReadStaticLoDelayReserved;
		this.ACSMWckReadStaticLoPulse_p2_ACSMWckReadStaticLoWidth = this.ACSMWckReadStaticLoPulse_p2.ACSMWckReadStaticLoWidth;
		this.ACSMWckReadStaticLoWidth = this.ACSMWckReadStaticLoPulse_p2.ACSMWckReadStaticLoWidth;
      this.ACSMWckReadStaticHiPulse_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckReadStaticHiPulse_p2::type_id::create("ACSMWckReadStaticHiPulse_p2",,get_full_name());
      if(this.ACSMWckReadStaticHiPulse_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckReadStaticHiPulse_p2.cg_bits.option.name = {get_name(), ".", "ACSMWckReadStaticHiPulse_p2_bits"};
      this.ACSMWckReadStaticHiPulse_p2.configure(this, null, "");
      this.ACSMWckReadStaticHiPulse_p2.build();
      this.default_map.add_reg(this.ACSMWckReadStaticHiPulse_p2, `UVM_REG_ADDR_WIDTH'h13A, "RW", 0);
		this.ACSMWckReadStaticHiPulse_p2_ACSMWckReadStaticHiDelay = this.ACSMWckReadStaticHiPulse_p2.ACSMWckReadStaticHiDelay;
		this.ACSMWckReadStaticHiDelay = this.ACSMWckReadStaticHiPulse_p2.ACSMWckReadStaticHiDelay;
		this.ACSMWckReadStaticHiPulse_p2_ACSMWckReadStaticHiDelayReserved = this.ACSMWckReadStaticHiPulse_p2.ACSMWckReadStaticHiDelayReserved;
		this.ACSMWckReadStaticHiDelayReserved = this.ACSMWckReadStaticHiPulse_p2.ACSMWckReadStaticHiDelayReserved;
		this.ACSMWckReadStaticHiPulse_p2_ACSMWckReadStaticHiWidth = this.ACSMWckReadStaticHiPulse_p2.ACSMWckReadStaticHiWidth;
		this.ACSMWckReadStaticHiWidth = this.ACSMWckReadStaticHiPulse_p2.ACSMWckReadStaticHiWidth;
      this.ACSMWckReadTogglePulse_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckReadTogglePulse_p2::type_id::create("ACSMWckReadTogglePulse_p2",,get_full_name());
      if(this.ACSMWckReadTogglePulse_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckReadTogglePulse_p2.cg_bits.option.name = {get_name(), ".", "ACSMWckReadTogglePulse_p2_bits"};
      this.ACSMWckReadTogglePulse_p2.configure(this, null, "");
      this.ACSMWckReadTogglePulse_p2.build();
      this.default_map.add_reg(this.ACSMWckReadTogglePulse_p2, `UVM_REG_ADDR_WIDTH'h13B, "RW", 0);
		this.ACSMWckReadTogglePulse_p2_ACSMWckReadToggleDelay = this.ACSMWckReadTogglePulse_p2.ACSMWckReadToggleDelay;
		this.ACSMWckReadToggleDelay = this.ACSMWckReadTogglePulse_p2.ACSMWckReadToggleDelay;
		this.ACSMWckReadTogglePulse_p2_ACSMWckReadToggleDelayReserved = this.ACSMWckReadTogglePulse_p2.ACSMWckReadToggleDelayReserved;
		this.ACSMWckReadToggleDelayReserved = this.ACSMWckReadTogglePulse_p2.ACSMWckReadToggleDelayReserved;
		this.ACSMWckReadTogglePulse_p2_ACSMWckReadToggleWidth = this.ACSMWckReadTogglePulse_p2.ACSMWckReadToggleWidth;
		this.ACSMWckReadToggleWidth = this.ACSMWckReadTogglePulse_p2.ACSMWckReadToggleWidth;
      this.ACSMWckReadFastTogglePulse_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckReadFastTogglePulse_p2::type_id::create("ACSMWckReadFastTogglePulse_p2",,get_full_name());
      if(this.ACSMWckReadFastTogglePulse_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckReadFastTogglePulse_p2.cg_bits.option.name = {get_name(), ".", "ACSMWckReadFastTogglePulse_p2_bits"};
      this.ACSMWckReadFastTogglePulse_p2.configure(this, null, "");
      this.ACSMWckReadFastTogglePulse_p2.build();
      this.default_map.add_reg(this.ACSMWckReadFastTogglePulse_p2, `UVM_REG_ADDR_WIDTH'h13C, "RW", 0);
		this.ACSMWckReadFastTogglePulse_p2_ACSMWckReadFastToggleDelay = this.ACSMWckReadFastTogglePulse_p2.ACSMWckReadFastToggleDelay;
		this.ACSMWckReadFastToggleDelay = this.ACSMWckReadFastTogglePulse_p2.ACSMWckReadFastToggleDelay;
		this.ACSMWckReadFastTogglePulse_p2_ACSMWckReadFastToggleDelayReserved = this.ACSMWckReadFastTogglePulse_p2.ACSMWckReadFastToggleDelayReserved;
		this.ACSMWckReadFastToggleDelayReserved = this.ACSMWckReadFastTogglePulse_p2.ACSMWckReadFastToggleDelayReserved;
		this.ACSMWckReadFastTogglePulse_p2_ACSMWckReadFastToggleWidth = this.ACSMWckReadFastTogglePulse_p2.ACSMWckReadFastToggleWidth;
		this.ACSMWckReadFastToggleWidth = this.ACSMWckReadFastTogglePulse_p2.ACSMWckReadFastToggleWidth;
      this.ACSMWckFreqSwStaticLoPulse_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwStaticLoPulse_p2::type_id::create("ACSMWckFreqSwStaticLoPulse_p2",,get_full_name());
      if(this.ACSMWckFreqSwStaticLoPulse_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckFreqSwStaticLoPulse_p2.cg_bits.option.name = {get_name(), ".", "ACSMWckFreqSwStaticLoPulse_p2_bits"};
      this.ACSMWckFreqSwStaticLoPulse_p2.configure(this, null, "");
      this.ACSMWckFreqSwStaticLoPulse_p2.build();
      this.default_map.add_reg(this.ACSMWckFreqSwStaticLoPulse_p2, `UVM_REG_ADDR_WIDTH'h13D, "RW", 0);
		this.ACSMWckFreqSwStaticLoPulse_p2_ACSMWckFreqSwStaticLoDelay = this.ACSMWckFreqSwStaticLoPulse_p2.ACSMWckFreqSwStaticLoDelay;
		this.ACSMWckFreqSwStaticLoDelay = this.ACSMWckFreqSwStaticLoPulse_p2.ACSMWckFreqSwStaticLoDelay;
		this.ACSMWckFreqSwStaticLoPulse_p2_ACSMWckFreqSwStaticLoDelayReserved = this.ACSMWckFreqSwStaticLoPulse_p2.ACSMWckFreqSwStaticLoDelayReserved;
		this.ACSMWckFreqSwStaticLoDelayReserved = this.ACSMWckFreqSwStaticLoPulse_p2.ACSMWckFreqSwStaticLoDelayReserved;
		this.ACSMWckFreqSwStaticLoPulse_p2_ACSMWckFreqSwStaticLoWidth = this.ACSMWckFreqSwStaticLoPulse_p2.ACSMWckFreqSwStaticLoWidth;
		this.ACSMWckFreqSwStaticLoWidth = this.ACSMWckFreqSwStaticLoPulse_p2.ACSMWckFreqSwStaticLoWidth;
      this.ACSMWckFreqSwStaticHiPulse_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwStaticHiPulse_p2::type_id::create("ACSMWckFreqSwStaticHiPulse_p2",,get_full_name());
      if(this.ACSMWckFreqSwStaticHiPulse_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckFreqSwStaticHiPulse_p2.cg_bits.option.name = {get_name(), ".", "ACSMWckFreqSwStaticHiPulse_p2_bits"};
      this.ACSMWckFreqSwStaticHiPulse_p2.configure(this, null, "");
      this.ACSMWckFreqSwStaticHiPulse_p2.build();
      this.default_map.add_reg(this.ACSMWckFreqSwStaticHiPulse_p2, `UVM_REG_ADDR_WIDTH'h13E, "RW", 0);
		this.ACSMWckFreqSwStaticHiPulse_p2_ACSMWckFreqSwStaticHiDelay = this.ACSMWckFreqSwStaticHiPulse_p2.ACSMWckFreqSwStaticHiDelay;
		this.ACSMWckFreqSwStaticHiDelay = this.ACSMWckFreqSwStaticHiPulse_p2.ACSMWckFreqSwStaticHiDelay;
		this.ACSMWckFreqSwStaticHiPulse_p2_ACSMWckFreqSwStaticHiDelayReserved = this.ACSMWckFreqSwStaticHiPulse_p2.ACSMWckFreqSwStaticHiDelayReserved;
		this.ACSMWckFreqSwStaticHiDelayReserved = this.ACSMWckFreqSwStaticHiPulse_p2.ACSMWckFreqSwStaticHiDelayReserved;
		this.ACSMWckFreqSwStaticHiPulse_p2_ACSMWckFreqSwStaticHiWidth = this.ACSMWckFreqSwStaticHiPulse_p2.ACSMWckFreqSwStaticHiWidth;
		this.ACSMWckFreqSwStaticHiWidth = this.ACSMWckFreqSwStaticHiPulse_p2.ACSMWckFreqSwStaticHiWidth;
      this.ACSMWckFreqSwTogglePulse_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwTogglePulse_p2::type_id::create("ACSMWckFreqSwTogglePulse_p2",,get_full_name());
      if(this.ACSMWckFreqSwTogglePulse_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckFreqSwTogglePulse_p2.cg_bits.option.name = {get_name(), ".", "ACSMWckFreqSwTogglePulse_p2_bits"};
      this.ACSMWckFreqSwTogglePulse_p2.configure(this, null, "");
      this.ACSMWckFreqSwTogglePulse_p2.build();
      this.default_map.add_reg(this.ACSMWckFreqSwTogglePulse_p2, `UVM_REG_ADDR_WIDTH'h13F, "RW", 0);
		this.ACSMWckFreqSwTogglePulse_p2_ACSMWckFreqSwToggleDelay = this.ACSMWckFreqSwTogglePulse_p2.ACSMWckFreqSwToggleDelay;
		this.ACSMWckFreqSwToggleDelay = this.ACSMWckFreqSwTogglePulse_p2.ACSMWckFreqSwToggleDelay;
		this.ACSMWckFreqSwTogglePulse_p2_ACSMWckFreqSwToggleDelayReserved = this.ACSMWckFreqSwTogglePulse_p2.ACSMWckFreqSwToggleDelayReserved;
		this.ACSMWckFreqSwToggleDelayReserved = this.ACSMWckFreqSwTogglePulse_p2.ACSMWckFreqSwToggleDelayReserved;
		this.ACSMWckFreqSwTogglePulse_p2_ACSMWckFreqSwToggleWidth = this.ACSMWckFreqSwTogglePulse_p2.ACSMWckFreqSwToggleWidth;
		this.ACSMWckFreqSwToggleWidth = this.ACSMWckFreqSwTogglePulse_p2.ACSMWckFreqSwToggleWidth;
      this.ACSMWckFreqSwFastTogglePulse_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreqSwFastTogglePulse_p2::type_id::create("ACSMWckFreqSwFastTogglePulse_p2",,get_full_name());
      if(this.ACSMWckFreqSwFastTogglePulse_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckFreqSwFastTogglePulse_p2.cg_bits.option.name = {get_name(), ".", "ACSMWckFreqSwFastTogglePulse_p2_bits"};
      this.ACSMWckFreqSwFastTogglePulse_p2.configure(this, null, "");
      this.ACSMWckFreqSwFastTogglePulse_p2.build();
      this.default_map.add_reg(this.ACSMWckFreqSwFastTogglePulse_p2, `UVM_REG_ADDR_WIDTH'h140, "RW", 0);
		this.ACSMWckFreqSwFastTogglePulse_p2_ACSMWckFreqSwFastToggleDelay = this.ACSMWckFreqSwFastTogglePulse_p2.ACSMWckFreqSwFastToggleDelay;
		this.ACSMWckFreqSwFastToggleDelay = this.ACSMWckFreqSwFastTogglePulse_p2.ACSMWckFreqSwFastToggleDelay;
		this.ACSMWckFreqSwFastTogglePulse_p2_ACSMWckFreqSwFastToggleDelayReserved = this.ACSMWckFreqSwFastTogglePulse_p2.ACSMWckFreqSwFastToggleDelayReserved;
		this.ACSMWckFreqSwFastToggleDelayReserved = this.ACSMWckFreqSwFastTogglePulse_p2.ACSMWckFreqSwFastToggleDelayReserved;
		this.ACSMWckFreqSwFastTogglePulse_p2_ACSMWckFreqSwFastToggleWidth = this.ACSMWckFreqSwFastTogglePulse_p2.ACSMWckFreqSwFastToggleWidth;
		this.ACSMWckFreqSwFastToggleWidth = this.ACSMWckFreqSwFastTogglePulse_p2.ACSMWckFreqSwFastToggleWidth;
      this.ACSMWckFreeRunMode_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMWckFreeRunMode_p2::type_id::create("ACSMWckFreeRunMode_p2",,get_full_name());
      if(this.ACSMWckFreeRunMode_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMWckFreeRunMode_p2.cg_bits.option.name = {get_name(), ".", "ACSMWckFreeRunMode_p2_bits"};
      this.ACSMWckFreeRunMode_p2.configure(this, null, "");
      this.ACSMWckFreeRunMode_p2.build();
      this.default_map.add_reg(this.ACSMWckFreeRunMode_p2, `UVM_REG_ADDR_WIDTH'h141, "RW", 0);
		this.ACSMWckFreeRunMode_p2_ACSMWckFreeRunMode_p2 = this.ACSMWckFreeRunMode_p2.ACSMWckFreeRunMode_p2;
      this.ACSMRptCntOverride_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRptCntOverride_p2::type_id::create("ACSMRptCntOverride_p2",,get_full_name());
      if(this.ACSMRptCntOverride_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMRptCntOverride_p2.cg_bits.option.name = {get_name(), ".", "ACSMRptCntOverride_p2_bits"};
      this.ACSMRptCntOverride_p2.configure(this, null, "");
      this.ACSMRptCntOverride_p2.build();
      this.default_map.add_reg(this.ACSMRptCntOverride_p2, `UVM_REG_ADDR_WIDTH'h145, "RW", 0);
		this.ACSMRptCntOverride_p2_ACSMRptCntOverride_p2 = this.ACSMRptCntOverride_p2.ACSMRptCntOverride_p2;
      this.ACSMRptCntDbl_p2 = ral_reg_DWC_DDRPHYA_PPGC0_p2_ACSMRptCntDbl_p2::type_id::create("ACSMRptCntDbl_p2",,get_full_name());
      if(this.ACSMRptCntDbl_p2.has_coverage(UVM_CVR_ALL))
      	this.ACSMRptCntDbl_p2.cg_bits.option.name = {get_name(), ".", "ACSMRptCntDbl_p2_bits"};
      this.ACSMRptCntDbl_p2.configure(this, null, "");
      this.ACSMRptCntDbl_p2.build();
      this.default_map.add_reg(this.ACSMRptCntDbl_p2, `UVM_REG_ADDR_WIDTH'h146, "RW", 0);
		this.ACSMRptCntDbl_p2_ACSMRptCntDbl_p2 = this.ACSMRptCntDbl_p2.ACSMRptCntDbl_p2;
   endfunction : build

	`uvm_object_utils(ral_block_DWC_DDRPHYA_PPGC0_p2)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_DDRPHYA_PPGC0_p2


endpackage
`endif
