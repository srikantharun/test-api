`ifndef RAL_DWC_DDRPHYA_AC1_P0_PKG
`define RAL_DWC_DDRPHYA_AC1_P0_PKG

package ral_DWC_DDRPHYA_AC1_p0_pkg;
import uvm_pkg::*;

class ral_reg_DWC_DDRPHYA_AC1_p0_AcPipeEn_p0 extends uvm_reg;
	rand uvm_reg_field AcPipeEn_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcPipeEn_p0: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcPipeEn_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcPipeEn_p0 = uvm_reg_field::type_id::create("AcPipeEn_p0",,get_full_name());
      this.AcPipeEn_p0.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcPipeEn_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcPipeEn_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_CKDllStopCal extends uvm_reg;
	rand uvm_reg_field CKDllStopCal;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CKDllStopCal: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_CKDllStopCal");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CKDllStopCal = uvm_reg_field::type_id::create("CKDllStopCal",,get_full_name());
      this.CKDllStopCal.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_CKDllStopCal)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_CKDllStopCal


class ral_reg_DWC_DDRPHYA_AC1_p0_CkVal_p0 extends uvm_reg;
	rand uvm_reg_field CkVal_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CkVal_p0: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_CkVal_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CkVal_p0 = uvm_reg_field::type_id::create("CkVal_p0",,get_full_name());
      this.CkVal_p0.configure(this, 2, 0, "RW", 0, 2'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_CkVal_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_CkVal_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_CkDisVal_p0 extends uvm_reg;
	uvm_reg_field Reserved;
	rand uvm_reg_field CkDisVal_p0;
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
	   CkDisVal_p0: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_CkDisVal_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.Reserved = uvm_reg_field::type_id::create("Reserved",,get_full_name());
      this.Reserved.configure(this, 1, 0, "RO", 1, 1'h0, 1, 0, 0);
      this.CkDisVal_p0 = uvm_reg_field::type_id::create("CkDisVal_p0",,get_full_name());
      this.CkDisVal_p0.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_CkDisVal_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_CkDisVal_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_DTOBypassEn extends uvm_reg;
	rand uvm_reg_field DTOBypassEn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DTOBypassEn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_DTOBypassEn");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DTOBypassEn = uvm_reg_field::type_id::create("DTOBypassEn",,get_full_name());
      this.DTOBypassEn.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_DTOBypassEn)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_DTOBypassEn


class ral_reg_DWC_DDRPHYA_AC1_p0_ACSingleEndedMode_p0 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACSingleEndedMode_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.SingleEndedCK = uvm_reg_field::type_id::create("SingleEndedCK",,get_full_name());
      this.SingleEndedCK.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACSingleEndedMode_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACSingleEndedMode_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_InitSeqControl extends uvm_reg;
	rand uvm_reg_field InhibitTxRdPtrBypassForce;
	rand uvm_reg_field InhibitTxRdPtrRstLclCal;
	rand uvm_reg_field InitControlRstLclCal;
	rand uvm_reg_field InhibitTxRdPtrRxReplLcdlInit;
	rand uvm_reg_field InitControlRxReplLcdlInit;
	rand uvm_reg_field InhibitTxRdPtrTXFIFOInit;
	rand uvm_reg_field InitControlTXFIFOInit;
	rand uvm_reg_field InhibitTxRdPtrDbDataPipeInit;
	rand uvm_reg_field InhibitTxRdPtrDbRxEnPhUpdInit;
	rand uvm_reg_field InitControlDbDataPipeInit;
	rand uvm_reg_field InhibitTxRdPtrDbPptInit;
	rand uvm_reg_field InitControlDbPptInit;
	rand uvm_reg_field InitControlDbRxEnPhUpdInit;
	rand uvm_reg_field InhibitTxRdPtrRxReplSeqInit;
	rand uvm_reg_field InitControlRxReplSeqInit;
	rand uvm_reg_field ReservedInitSeqControl;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   InhibitTxRdPtrBypassForce: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   InhibitTxRdPtrRstLclCal: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   InitControlRstLclCal: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   InhibitTxRdPtrRxReplLcdlInit: coverpoint {m_data[3:3], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   InitControlRxReplLcdlInit: coverpoint {m_data[4:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   InhibitTxRdPtrTXFIFOInit: coverpoint {m_data[5:5], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   InitControlTXFIFOInit: coverpoint {m_data[6:6], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   InhibitTxRdPtrDbDataPipeInit: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   InhibitTxRdPtrDbRxEnPhUpdInit: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   InitControlDbDataPipeInit: coverpoint {m_data[9:9], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   InhibitTxRdPtrDbPptInit: coverpoint {m_data[10:10], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   InitControlDbPptInit: coverpoint {m_data[11:11], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   InitControlDbRxEnPhUpdInit: coverpoint {m_data[12:12], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   InhibitTxRdPtrRxReplSeqInit: coverpoint {m_data[13:13], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   InitControlRxReplSeqInit: coverpoint {m_data[14:14], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ReservedInitSeqControl: coverpoint {m_data[15:15], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_InitSeqControl");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.InhibitTxRdPtrBypassForce = uvm_reg_field::type_id::create("InhibitTxRdPtrBypassForce",,get_full_name());
      this.InhibitTxRdPtrBypassForce.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.InhibitTxRdPtrRstLclCal = uvm_reg_field::type_id::create("InhibitTxRdPtrRstLclCal",,get_full_name());
      this.InhibitTxRdPtrRstLclCal.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.InitControlRstLclCal = uvm_reg_field::type_id::create("InitControlRstLclCal",,get_full_name());
      this.InitControlRstLclCal.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
      this.InhibitTxRdPtrRxReplLcdlInit = uvm_reg_field::type_id::create("InhibitTxRdPtrRxReplLcdlInit",,get_full_name());
      this.InhibitTxRdPtrRxReplLcdlInit.configure(this, 1, 3, "RW", 0, 1'h0, 1, 0, 0);
      this.InitControlRxReplLcdlInit = uvm_reg_field::type_id::create("InitControlRxReplLcdlInit",,get_full_name());
      this.InitControlRxReplLcdlInit.configure(this, 1, 4, "RW", 0, 1'h0, 1, 0, 0);
      this.InhibitTxRdPtrTXFIFOInit = uvm_reg_field::type_id::create("InhibitTxRdPtrTXFIFOInit",,get_full_name());
      this.InhibitTxRdPtrTXFIFOInit.configure(this, 1, 5, "RW", 0, 1'h0, 1, 0, 0);
      this.InitControlTXFIFOInit = uvm_reg_field::type_id::create("InitControlTXFIFOInit",,get_full_name());
      this.InitControlTXFIFOInit.configure(this, 1, 6, "RW", 0, 1'h0, 1, 0, 0);
      this.InhibitTxRdPtrDbDataPipeInit = uvm_reg_field::type_id::create("InhibitTxRdPtrDbDataPipeInit",,get_full_name());
      this.InhibitTxRdPtrDbDataPipeInit.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.InhibitTxRdPtrDbRxEnPhUpdInit = uvm_reg_field::type_id::create("InhibitTxRdPtrDbRxEnPhUpdInit",,get_full_name());
      this.InhibitTxRdPtrDbRxEnPhUpdInit.configure(this, 1, 8, "RW", 0, 1'h0, 1, 0, 0);
      this.InitControlDbDataPipeInit = uvm_reg_field::type_id::create("InitControlDbDataPipeInit",,get_full_name());
      this.InitControlDbDataPipeInit.configure(this, 1, 9, "RW", 0, 1'h0, 1, 0, 0);
      this.InhibitTxRdPtrDbPptInit = uvm_reg_field::type_id::create("InhibitTxRdPtrDbPptInit",,get_full_name());
      this.InhibitTxRdPtrDbPptInit.configure(this, 1, 10, "RW", 0, 1'h0, 1, 0, 0);
      this.InitControlDbPptInit = uvm_reg_field::type_id::create("InitControlDbPptInit",,get_full_name());
      this.InitControlDbPptInit.configure(this, 1, 11, "RW", 0, 1'h0, 1, 0, 0);
      this.InitControlDbRxEnPhUpdInit = uvm_reg_field::type_id::create("InitControlDbRxEnPhUpdInit",,get_full_name());
      this.InitControlDbRxEnPhUpdInit.configure(this, 1, 12, "RW", 0, 1'h0, 1, 0, 0);
      this.InhibitTxRdPtrRxReplSeqInit = uvm_reg_field::type_id::create("InhibitTxRdPtrRxReplSeqInit",,get_full_name());
      this.InhibitTxRdPtrRxReplSeqInit.configure(this, 1, 13, "RW", 0, 1'h0, 1, 0, 0);
      this.InitControlRxReplSeqInit = uvm_reg_field::type_id::create("InitControlRxReplSeqInit",,get_full_name());
      this.InitControlRxReplSeqInit.configure(this, 1, 14, "RW", 0, 1'h0, 1, 0, 0);
      this.ReservedInitSeqControl = uvm_reg_field::type_id::create("ReservedInitSeqControl",,get_full_name());
      this.ReservedInitSeqControl.configure(this, 1, 15, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_InitSeqControl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_InitSeqControl


class ral_reg_DWC_DDRPHYA_AC1_p0_MtestMuxSel extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_MtestMuxSel");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MtestMuxSel = uvm_reg_field::type_id::create("MtestMuxSel",,get_full_name());
      this.MtestMuxSel.configure(this, 10, 0, "RW", 0, 10'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_MtestMuxSel)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_MtestMuxSel


class ral_reg_DWC_DDRPHYA_AC1_p0_PorControl extends uvm_reg;
	rand uvm_reg_field PwrOkDlyCtrl;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PwrOkDlyCtrl: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_PorControl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PwrOkDlyCtrl = uvm_reg_field::type_id::create("PwrOkDlyCtrl",,get_full_name());
      this.PwrOkDlyCtrl.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_PorControl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_PorControl


class ral_reg_DWC_DDRPHYA_AC1_p0_ClrPORMemReset extends uvm_reg;
	rand uvm_reg_field ClrPORMemReset;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ClrPORMemReset: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_ClrPORMemReset");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ClrPORMemReset = uvm_reg_field::type_id::create("ClrPORMemReset",,get_full_name());
      this.ClrPORMemReset.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ClrPORMemReset)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ClrPORMemReset


class ral_reg_DWC_DDRPHYA_AC1_p0_MemResetL extends uvm_reg;
	rand uvm_reg_field MemResetLValue;
	rand uvm_reg_field ProtectMemReset;
	rand uvm_reg_field AsyncMemResetLRxMode;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   MemResetLValue: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ProtectMemReset: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   AsyncMemResetLRxMode: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_MemResetL");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MemResetLValue = uvm_reg_field::type_id::create("MemResetLValue",,get_full_name());
      this.MemResetLValue.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 0);
      this.ProtectMemReset = uvm_reg_field::type_id::create("ProtectMemReset",,get_full_name());
      this.ProtectMemReset.configure(this, 1, 1, "RW", 0, 1'h1, 1, 0, 0);
      this.AsyncMemResetLRxMode = uvm_reg_field::type_id::create("AsyncMemResetLRxMode",,get_full_name());
      this.AsyncMemResetLRxMode.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_MemResetL)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_MemResetL


class ral_reg_DWC_DDRPHYA_AC1_p0_CMOSxHardMacroModeSel extends uvm_reg;
	rand uvm_reg_field CMOSxHardMacroModeSel;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CMOSxHardMacroModeSel: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_CMOSxHardMacroModeSel");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CMOSxHardMacroModeSel = uvm_reg_field::type_id::create("CMOSxHardMacroModeSel",,get_full_name());
      this.CMOSxHardMacroModeSel.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_CMOSxHardMacroModeSel)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_CMOSxHardMacroModeSel


class ral_reg_DWC_DDRPHYA_AC1_p0_RxAcVrefControl_p0 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_RxAcVrefControl_p0");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_RxAcVrefControl_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_RxAcVrefControl_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_MemResetLStatus extends uvm_reg;
	uvm_reg_field PORMemReset;
	uvm_reg_field AsyncMemResetLRxData;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PORMemReset: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   AsyncMemResetLRxData: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_MemResetLStatus");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PORMemReset = uvm_reg_field::type_id::create("PORMemReset",,get_full_name());
      this.PORMemReset.configure(this, 1, 0, "RO", 1, 1'h0, 1, 0, 0);
      this.AsyncMemResetLRxData = uvm_reg_field::type_id::create("AsyncMemResetLRxData",,get_full_name());
      this.AsyncMemResetLRxData.configure(this, 1, 1, "RO", 1, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_MemResetLStatus)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_MemResetLStatus


class ral_reg_DWC_DDRPHYA_AC1_p0_ACDlyScaleGatingDisable extends uvm_reg;
	rand uvm_reg_field ACDlyScaleGatingDisable;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACDlyScaleGatingDisable: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACDlyScaleGatingDisable");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACDlyScaleGatingDisable = uvm_reg_field::type_id::create("ACDlyScaleGatingDisable",,get_full_name());
      this.ACDlyScaleGatingDisable.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACDlyScaleGatingDisable)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACDlyScaleGatingDisable


class ral_reg_DWC_DDRPHYA_AC1_p0_LcdlCalControl extends uvm_reg;
	rand uvm_reg_field LcdlCalResetRelock;
	rand uvm_reg_field LcdlCalStop;
	rand uvm_reg_field LcdlUpdTrackDis;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   LcdlCalResetRelock: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   LcdlCalStop: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   LcdlUpdTrackDis: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_LcdlCalControl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.LcdlCalResetRelock = uvm_reg_field::type_id::create("LcdlCalResetRelock",,get_full_name());
      this.LcdlCalResetRelock.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.LcdlCalStop = uvm_reg_field::type_id::create("LcdlCalStop",,get_full_name());
      this.LcdlCalStop.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.LcdlUpdTrackDis = uvm_reg_field::type_id::create("LcdlUpdTrackDis",,get_full_name());
      this.LcdlUpdTrackDis.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_LcdlCalControl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_LcdlCalControl


class ral_reg_DWC_DDRPHYA_AC1_p0_ACParityInvert extends uvm_reg;
	rand uvm_reg_field ACParityInvert;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACParityInvert: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACParityInvert");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACParityInvert = uvm_reg_field::type_id::create("ACParityInvert",,get_full_name());
      this.ACParityInvert.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACParityInvert)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACParityInvert


class ral_reg_DWC_DDRPHYA_AC1_p0_ACPulseDllUpdatePhase extends uvm_reg;
	rand uvm_reg_field ACPulseDllUpdatePhase;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACPulseDllUpdatePhase: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACPulseDllUpdatePhase");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACPulseDllUpdatePhase = uvm_reg_field::type_id::create("ACPulseDllUpdatePhase",,get_full_name());
      this.ACPulseDllUpdatePhase.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACPulseDllUpdatePhase)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACPulseDllUpdatePhase


class ral_reg_DWC_DDRPHYA_AC1_p0_ScratchPadAC extends uvm_reg;
	rand uvm_reg_field ScratchPadAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ScratchPadAC: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ScratchPadAC");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ScratchPadAC = uvm_reg_field::type_id::create("ScratchPadAC",,get_full_name());
      this.ScratchPadAC.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ScratchPadAC)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ScratchPadAC


class ral_reg_DWC_DDRPHYA_AC1_p0_ATestMode extends uvm_reg;
	rand uvm_reg_field ATestPrbsEn;
	rand uvm_reg_field ATestPrbs7or15Mode;
	rand uvm_reg_field ReservedATestMode42;
	rand uvm_reg_field ATestPrbsChkmode;
	rand uvm_reg_field PrbsDdrMode;
	rand uvm_reg_field ReservedATestMode7;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ATestPrbsEn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ATestPrbs7or15Mode: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ReservedATestMode42: coverpoint {m_data[4:2], m_is_read} iff(m_be) {
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
	   ATestPrbsChkmode: coverpoint {m_data[5:5], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PrbsDdrMode: coverpoint {m_data[6:6], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ReservedATestMode7: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_ATestMode");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ATestPrbsEn = uvm_reg_field::type_id::create("ATestPrbsEn",,get_full_name());
      this.ATestPrbsEn.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.ATestPrbs7or15Mode = uvm_reg_field::type_id::create("ATestPrbs7or15Mode",,get_full_name());
      this.ATestPrbs7or15Mode.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.ReservedATestMode42 = uvm_reg_field::type_id::create("ReservedATestMode42",,get_full_name());
      this.ReservedATestMode42.configure(this, 3, 2, "RW", 0, 3'h0, 1, 0, 0);
      this.ATestPrbsChkmode = uvm_reg_field::type_id::create("ATestPrbsChkmode",,get_full_name());
      this.ATestPrbsChkmode.configure(this, 1, 5, "RW", 0, 1'h0, 1, 0, 0);
      this.PrbsDdrMode = uvm_reg_field::type_id::create("PrbsDdrMode",,get_full_name());
      this.PrbsDdrMode.configure(this, 1, 6, "RW", 0, 1'h0, 1, 0, 0);
      this.ReservedATestMode7 = uvm_reg_field::type_id::create("ReservedATestMode7",,get_full_name());
      this.ReservedATestMode7.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ATestMode)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ATestMode


class ral_reg_DWC_DDRPHYA_AC1_p0_AcDigStrobeGenSel extends uvm_reg;
	rand uvm_reg_field AcDigStrobeGenSel;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcDigStrobeGenSel: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcDigStrobeGenSel");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcDigStrobeGenSel = uvm_reg_field::type_id::create("AcDigStrobeGenSel",,get_full_name());
      this.AcDigStrobeGenSel.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcDigStrobeGenSel)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcDigStrobeGenSel


class ral_reg_DWC_DDRPHYA_AC1_p0_AcDigStrobePat extends uvm_reg;
	rand uvm_reg_field AcDigStrobePat;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcDigStrobePat: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcDigStrobePat");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcDigStrobePat = uvm_reg_field::type_id::create("AcDigStrobePat",,get_full_name());
      this.AcDigStrobePat.configure(this, 4, 0, "RW", 0, 4'ha, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcDigStrobePat)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcDigStrobePat


class ral_reg_DWC_DDRPHYA_AC1_p0_AcOdtEn extends uvm_reg;
	rand uvm_reg_field AcOdtEn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcOdtEn: coverpoint {m_data[9:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcOdtEn");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcOdtEn = uvm_reg_field::type_id::create("AcOdtEn",,get_full_name());
      this.AcOdtEn.configure(this, 10, 0, "RW", 0, 10'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcOdtEn)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcOdtEn


class ral_reg_DWC_DDRPHYA_AC1_p0_AcRxStrobeEnPat extends uvm_reg;
	rand uvm_reg_field AcRxStrobeEnPat;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcRxStrobeEnPat: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcRxStrobeEnPat");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcRxStrobeEnPat = uvm_reg_field::type_id::create("AcRxStrobeEnPat",,get_full_name());
      this.AcRxStrobeEnPat.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcRxStrobeEnPat)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcRxStrobeEnPat


class ral_reg_DWC_DDRPHYA_AC1_p0_ATxDlySelect_p0 extends uvm_reg;
	rand uvm_reg_field ATxDlySelect_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ATxDlySelect_p0: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ATxDlySelect_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ATxDlySelect_p0 = uvm_reg_field::type_id::create("ATxDlySelect_p0",,get_full_name());
      this.ATxDlySelect_p0.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ATxDlySelect_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ATxDlySelect_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_MapCA0toDfi extends uvm_reg;
	rand uvm_reg_field MapCA0toDfi;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   MapCA0toDfi: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_MapCA0toDfi");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MapCA0toDfi = uvm_reg_field::type_id::create("MapCA0toDfi",,get_full_name());
      this.MapCA0toDfi.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_MapCA0toDfi)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_MapCA0toDfi


class ral_reg_DWC_DDRPHYA_AC1_p0_MapCA1toDfi extends uvm_reg;
	rand uvm_reg_field MapCA1toDfi;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   MapCA1toDfi: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_MapCA1toDfi");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MapCA1toDfi = uvm_reg_field::type_id::create("MapCA1toDfi",,get_full_name());
      this.MapCA1toDfi.configure(this, 4, 0, "RW", 0, 4'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_MapCA1toDfi)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_MapCA1toDfi


class ral_reg_DWC_DDRPHYA_AC1_p0_MapCA2toDfi extends uvm_reg;
	rand uvm_reg_field MapCA2toDfi;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   MapCA2toDfi: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_MapCA2toDfi");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MapCA2toDfi = uvm_reg_field::type_id::create("MapCA2toDfi",,get_full_name());
      this.MapCA2toDfi.configure(this, 4, 0, "RW", 0, 4'h2, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_MapCA2toDfi)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_MapCA2toDfi


class ral_reg_DWC_DDRPHYA_AC1_p0_MapCA3toDfi extends uvm_reg;
	rand uvm_reg_field MapCA3toDfi;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   MapCA3toDfi: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_MapCA3toDfi");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MapCA3toDfi = uvm_reg_field::type_id::create("MapCA3toDfi",,get_full_name());
      this.MapCA3toDfi.configure(this, 4, 0, "RW", 0, 4'h3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_MapCA3toDfi)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_MapCA3toDfi


class ral_reg_DWC_DDRPHYA_AC1_p0_MapCA4toDfi extends uvm_reg;
	rand uvm_reg_field MapCA4toDfi;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   MapCA4toDfi: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_MapCA4toDfi");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MapCA4toDfi = uvm_reg_field::type_id::create("MapCA4toDfi",,get_full_name());
      this.MapCA4toDfi.configure(this, 4, 0, "RW", 0, 4'h4, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_MapCA4toDfi)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_MapCA4toDfi


class ral_reg_DWC_DDRPHYA_AC1_p0_MapCA5toDfi extends uvm_reg;
	rand uvm_reg_field MapCA5toDfi;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   MapCA5toDfi: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_MapCA5toDfi");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MapCA5toDfi = uvm_reg_field::type_id::create("MapCA5toDfi",,get_full_name());
      this.MapCA5toDfi.configure(this, 4, 0, "RW", 0, 4'h5, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_MapCA5toDfi)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_MapCA5toDfi


class ral_reg_DWC_DDRPHYA_AC1_p0_MapCA6toDfi extends uvm_reg;
	rand uvm_reg_field MapCA6toDfi;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   MapCA6toDfi: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_MapCA6toDfi");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MapCA6toDfi = uvm_reg_field::type_id::create("MapCA6toDfi",,get_full_name());
      this.MapCA6toDfi.configure(this, 4, 0, "RW", 0, 4'h6, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_MapCA6toDfi)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_MapCA6toDfi


class ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcTxMode extends uvm_reg;
	rand uvm_reg_field AsyncAcTxMode;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AsyncAcTxMode: coverpoint {m_data[13:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {15'b?????????????00};
	      wildcard bins bit_0_wr_as_1 = {15'b?????????????10};
	      wildcard bins bit_0_rd_as_0 = {15'b?????????????01};
	      wildcard bins bit_0_rd_as_1 = {15'b?????????????11};
	      wildcard bins bit_1_wr_as_0 = {15'b????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {15'b????????????1?0};
	      wildcard bins bit_1_rd_as_0 = {15'b????????????0?1};
	      wildcard bins bit_1_rd_as_1 = {15'b????????????1?1};
	      wildcard bins bit_2_wr_as_0 = {15'b???????????0??0};
	      wildcard bins bit_2_wr_as_1 = {15'b???????????1??0};
	      wildcard bins bit_2_rd_as_0 = {15'b???????????0??1};
	      wildcard bins bit_2_rd_as_1 = {15'b???????????1??1};
	      wildcard bins bit_3_wr_as_0 = {15'b??????????0???0};
	      wildcard bins bit_3_wr_as_1 = {15'b??????????1???0};
	      wildcard bins bit_3_rd_as_0 = {15'b??????????0???1};
	      wildcard bins bit_3_rd_as_1 = {15'b??????????1???1};
	      wildcard bins bit_4_wr_as_0 = {15'b?????????0????0};
	      wildcard bins bit_4_wr_as_1 = {15'b?????????1????0};
	      wildcard bins bit_4_rd_as_0 = {15'b?????????0????1};
	      wildcard bins bit_4_rd_as_1 = {15'b?????????1????1};
	      wildcard bins bit_5_wr_as_0 = {15'b????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {15'b????????1?????0};
	      wildcard bins bit_5_rd_as_0 = {15'b????????0?????1};
	      wildcard bins bit_5_rd_as_1 = {15'b????????1?????1};
	      wildcard bins bit_6_wr_as_0 = {15'b???????0??????0};
	      wildcard bins bit_6_wr_as_1 = {15'b???????1??????0};
	      wildcard bins bit_6_rd_as_0 = {15'b???????0??????1};
	      wildcard bins bit_6_rd_as_1 = {15'b???????1??????1};
	      wildcard bins bit_7_wr_as_0 = {15'b??????0???????0};
	      wildcard bins bit_7_wr_as_1 = {15'b??????1???????0};
	      wildcard bins bit_7_rd_as_0 = {15'b??????0???????1};
	      wildcard bins bit_7_rd_as_1 = {15'b??????1???????1};
	      wildcard bins bit_8_wr_as_0 = {15'b?????0????????0};
	      wildcard bins bit_8_wr_as_1 = {15'b?????1????????0};
	      wildcard bins bit_8_rd_as_0 = {15'b?????0????????1};
	      wildcard bins bit_8_rd_as_1 = {15'b?????1????????1};
	      wildcard bins bit_9_wr_as_0 = {15'b????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {15'b????1?????????0};
	      wildcard bins bit_9_rd_as_0 = {15'b????0?????????1};
	      wildcard bins bit_9_rd_as_1 = {15'b????1?????????1};
	      wildcard bins bit_10_wr_as_0 = {15'b???0??????????0};
	      wildcard bins bit_10_wr_as_1 = {15'b???1??????????0};
	      wildcard bins bit_10_rd_as_0 = {15'b???0??????????1};
	      wildcard bins bit_10_rd_as_1 = {15'b???1??????????1};
	      wildcard bins bit_11_wr_as_0 = {15'b??0???????????0};
	      wildcard bins bit_11_wr_as_1 = {15'b??1???????????0};
	      wildcard bins bit_11_rd_as_0 = {15'b??0???????????1};
	      wildcard bins bit_11_rd_as_1 = {15'b??1???????????1};
	      wildcard bins bit_12_wr_as_0 = {15'b?0????????????0};
	      wildcard bins bit_12_wr_as_1 = {15'b?1????????????0};
	      wildcard bins bit_12_rd_as_0 = {15'b?0????????????1};
	      wildcard bins bit_12_rd_as_1 = {15'b?1????????????1};
	      wildcard bins bit_13_wr_as_0 = {15'b0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {15'b1?????????????0};
	      wildcard bins bit_13_rd_as_0 = {15'b0?????????????1};
	      wildcard bins bit_13_rd_as_1 = {15'b1?????????????1};
	      option.weight = 56;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AsyncAcTxMode");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AsyncAcTxMode = uvm_reg_field::type_id::create("AsyncAcTxMode",,get_full_name());
      this.AsyncAcTxMode.configure(this, 14, 0, "RW", 0, 14'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcTxMode)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcTxMode


class ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcRxMode extends uvm_reg;
	rand uvm_reg_field AsyncAcRxMode;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AsyncAcRxMode: coverpoint {m_data[13:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {15'b?????????????00};
	      wildcard bins bit_0_wr_as_1 = {15'b?????????????10};
	      wildcard bins bit_0_rd_as_0 = {15'b?????????????01};
	      wildcard bins bit_0_rd_as_1 = {15'b?????????????11};
	      wildcard bins bit_1_wr_as_0 = {15'b????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {15'b????????????1?0};
	      wildcard bins bit_1_rd_as_0 = {15'b????????????0?1};
	      wildcard bins bit_1_rd_as_1 = {15'b????????????1?1};
	      wildcard bins bit_2_wr_as_0 = {15'b???????????0??0};
	      wildcard bins bit_2_wr_as_1 = {15'b???????????1??0};
	      wildcard bins bit_2_rd_as_0 = {15'b???????????0??1};
	      wildcard bins bit_2_rd_as_1 = {15'b???????????1??1};
	      wildcard bins bit_3_wr_as_0 = {15'b??????????0???0};
	      wildcard bins bit_3_wr_as_1 = {15'b??????????1???0};
	      wildcard bins bit_3_rd_as_0 = {15'b??????????0???1};
	      wildcard bins bit_3_rd_as_1 = {15'b??????????1???1};
	      wildcard bins bit_4_wr_as_0 = {15'b?????????0????0};
	      wildcard bins bit_4_wr_as_1 = {15'b?????????1????0};
	      wildcard bins bit_4_rd_as_0 = {15'b?????????0????1};
	      wildcard bins bit_4_rd_as_1 = {15'b?????????1????1};
	      wildcard bins bit_5_wr_as_0 = {15'b????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {15'b????????1?????0};
	      wildcard bins bit_5_rd_as_0 = {15'b????????0?????1};
	      wildcard bins bit_5_rd_as_1 = {15'b????????1?????1};
	      wildcard bins bit_6_wr_as_0 = {15'b???????0??????0};
	      wildcard bins bit_6_wr_as_1 = {15'b???????1??????0};
	      wildcard bins bit_6_rd_as_0 = {15'b???????0??????1};
	      wildcard bins bit_6_rd_as_1 = {15'b???????1??????1};
	      wildcard bins bit_7_wr_as_0 = {15'b??????0???????0};
	      wildcard bins bit_7_wr_as_1 = {15'b??????1???????0};
	      wildcard bins bit_7_rd_as_0 = {15'b??????0???????1};
	      wildcard bins bit_7_rd_as_1 = {15'b??????1???????1};
	      wildcard bins bit_8_wr_as_0 = {15'b?????0????????0};
	      wildcard bins bit_8_wr_as_1 = {15'b?????1????????0};
	      wildcard bins bit_8_rd_as_0 = {15'b?????0????????1};
	      wildcard bins bit_8_rd_as_1 = {15'b?????1????????1};
	      wildcard bins bit_9_wr_as_0 = {15'b????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {15'b????1?????????0};
	      wildcard bins bit_9_rd_as_0 = {15'b????0?????????1};
	      wildcard bins bit_9_rd_as_1 = {15'b????1?????????1};
	      wildcard bins bit_10_wr_as_0 = {15'b???0??????????0};
	      wildcard bins bit_10_wr_as_1 = {15'b???1??????????0};
	      wildcard bins bit_10_rd_as_0 = {15'b???0??????????1};
	      wildcard bins bit_10_rd_as_1 = {15'b???1??????????1};
	      wildcard bins bit_11_wr_as_0 = {15'b??0???????????0};
	      wildcard bins bit_11_wr_as_1 = {15'b??1???????????0};
	      wildcard bins bit_11_rd_as_0 = {15'b??0???????????1};
	      wildcard bins bit_11_rd_as_1 = {15'b??1???????????1};
	      wildcard bins bit_12_wr_as_0 = {15'b?0????????????0};
	      wildcard bins bit_12_wr_as_1 = {15'b?1????????????0};
	      wildcard bins bit_12_rd_as_0 = {15'b?0????????????1};
	      wildcard bins bit_12_rd_as_1 = {15'b?1????????????1};
	      wildcard bins bit_13_wr_as_0 = {15'b0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {15'b1?????????????0};
	      wildcard bins bit_13_rd_as_0 = {15'b0?????????????1};
	      wildcard bins bit_13_rd_as_1 = {15'b1?????????????1};
	      option.weight = 56;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AsyncAcRxMode");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AsyncAcRxMode = uvm_reg_field::type_id::create("AsyncAcRxMode",,get_full_name());
      this.AsyncAcRxMode.configure(this, 14, 0, "RW", 0, 14'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcRxMode)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcRxMode


class ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcTxEn extends uvm_reg;
	rand uvm_reg_field AsyncAcTxEn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AsyncAcTxEn: coverpoint {m_data[13:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {15'b?????????????00};
	      wildcard bins bit_0_wr_as_1 = {15'b?????????????10};
	      wildcard bins bit_0_rd_as_0 = {15'b?????????????01};
	      wildcard bins bit_0_rd_as_1 = {15'b?????????????11};
	      wildcard bins bit_1_wr_as_0 = {15'b????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {15'b????????????1?0};
	      wildcard bins bit_1_rd_as_0 = {15'b????????????0?1};
	      wildcard bins bit_1_rd_as_1 = {15'b????????????1?1};
	      wildcard bins bit_2_wr_as_0 = {15'b???????????0??0};
	      wildcard bins bit_2_wr_as_1 = {15'b???????????1??0};
	      wildcard bins bit_2_rd_as_0 = {15'b???????????0??1};
	      wildcard bins bit_2_rd_as_1 = {15'b???????????1??1};
	      wildcard bins bit_3_wr_as_0 = {15'b??????????0???0};
	      wildcard bins bit_3_wr_as_1 = {15'b??????????1???0};
	      wildcard bins bit_3_rd_as_0 = {15'b??????????0???1};
	      wildcard bins bit_3_rd_as_1 = {15'b??????????1???1};
	      wildcard bins bit_4_wr_as_0 = {15'b?????????0????0};
	      wildcard bins bit_4_wr_as_1 = {15'b?????????1????0};
	      wildcard bins bit_4_rd_as_0 = {15'b?????????0????1};
	      wildcard bins bit_4_rd_as_1 = {15'b?????????1????1};
	      wildcard bins bit_5_wr_as_0 = {15'b????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {15'b????????1?????0};
	      wildcard bins bit_5_rd_as_0 = {15'b????????0?????1};
	      wildcard bins bit_5_rd_as_1 = {15'b????????1?????1};
	      wildcard bins bit_6_wr_as_0 = {15'b???????0??????0};
	      wildcard bins bit_6_wr_as_1 = {15'b???????1??????0};
	      wildcard bins bit_6_rd_as_0 = {15'b???????0??????1};
	      wildcard bins bit_6_rd_as_1 = {15'b???????1??????1};
	      wildcard bins bit_7_wr_as_0 = {15'b??????0???????0};
	      wildcard bins bit_7_wr_as_1 = {15'b??????1???????0};
	      wildcard bins bit_7_rd_as_0 = {15'b??????0???????1};
	      wildcard bins bit_7_rd_as_1 = {15'b??????1???????1};
	      wildcard bins bit_8_wr_as_0 = {15'b?????0????????0};
	      wildcard bins bit_8_wr_as_1 = {15'b?????1????????0};
	      wildcard bins bit_8_rd_as_0 = {15'b?????0????????1};
	      wildcard bins bit_8_rd_as_1 = {15'b?????1????????1};
	      wildcard bins bit_9_wr_as_0 = {15'b????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {15'b????1?????????0};
	      wildcard bins bit_9_rd_as_0 = {15'b????0?????????1};
	      wildcard bins bit_9_rd_as_1 = {15'b????1?????????1};
	      wildcard bins bit_10_wr_as_0 = {15'b???0??????????0};
	      wildcard bins bit_10_wr_as_1 = {15'b???1??????????0};
	      wildcard bins bit_10_rd_as_0 = {15'b???0??????????1};
	      wildcard bins bit_10_rd_as_1 = {15'b???1??????????1};
	      wildcard bins bit_11_wr_as_0 = {15'b??0???????????0};
	      wildcard bins bit_11_wr_as_1 = {15'b??1???????????0};
	      wildcard bins bit_11_rd_as_0 = {15'b??0???????????1};
	      wildcard bins bit_11_rd_as_1 = {15'b??1???????????1};
	      wildcard bins bit_12_wr_as_0 = {15'b?0????????????0};
	      wildcard bins bit_12_wr_as_1 = {15'b?1????????????0};
	      wildcard bins bit_12_rd_as_0 = {15'b?0????????????1};
	      wildcard bins bit_12_rd_as_1 = {15'b?1????????????1};
	      wildcard bins bit_13_wr_as_0 = {15'b0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {15'b1?????????????0};
	      wildcard bins bit_13_rd_as_0 = {15'b0?????????????1};
	      wildcard bins bit_13_rd_as_1 = {15'b1?????????????1};
	      option.weight = 56;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AsyncAcTxEn");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AsyncAcTxEn = uvm_reg_field::type_id::create("AsyncAcTxEn",,get_full_name());
      this.AsyncAcTxEn.configure(this, 14, 0, "RW", 0, 14'h3f00, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcTxEn)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcTxEn


class ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcTxData extends uvm_reg;
	rand uvm_reg_field AsyncAcTxData;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AsyncAcTxData: coverpoint {m_data[13:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {15'b?????????????00};
	      wildcard bins bit_0_wr_as_1 = {15'b?????????????10};
	      wildcard bins bit_0_rd_as_0 = {15'b?????????????01};
	      wildcard bins bit_0_rd_as_1 = {15'b?????????????11};
	      wildcard bins bit_1_wr_as_0 = {15'b????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {15'b????????????1?0};
	      wildcard bins bit_1_rd_as_0 = {15'b????????????0?1};
	      wildcard bins bit_1_rd_as_1 = {15'b????????????1?1};
	      wildcard bins bit_2_wr_as_0 = {15'b???????????0??0};
	      wildcard bins bit_2_wr_as_1 = {15'b???????????1??0};
	      wildcard bins bit_2_rd_as_0 = {15'b???????????0??1};
	      wildcard bins bit_2_rd_as_1 = {15'b???????????1??1};
	      wildcard bins bit_3_wr_as_0 = {15'b??????????0???0};
	      wildcard bins bit_3_wr_as_1 = {15'b??????????1???0};
	      wildcard bins bit_3_rd_as_0 = {15'b??????????0???1};
	      wildcard bins bit_3_rd_as_1 = {15'b??????????1???1};
	      wildcard bins bit_4_wr_as_0 = {15'b?????????0????0};
	      wildcard bins bit_4_wr_as_1 = {15'b?????????1????0};
	      wildcard bins bit_4_rd_as_0 = {15'b?????????0????1};
	      wildcard bins bit_4_rd_as_1 = {15'b?????????1????1};
	      wildcard bins bit_5_wr_as_0 = {15'b????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {15'b????????1?????0};
	      wildcard bins bit_5_rd_as_0 = {15'b????????0?????1};
	      wildcard bins bit_5_rd_as_1 = {15'b????????1?????1};
	      wildcard bins bit_6_wr_as_0 = {15'b???????0??????0};
	      wildcard bins bit_6_wr_as_1 = {15'b???????1??????0};
	      wildcard bins bit_6_rd_as_0 = {15'b???????0??????1};
	      wildcard bins bit_6_rd_as_1 = {15'b???????1??????1};
	      wildcard bins bit_7_wr_as_0 = {15'b??????0???????0};
	      wildcard bins bit_7_wr_as_1 = {15'b??????1???????0};
	      wildcard bins bit_7_rd_as_0 = {15'b??????0???????1};
	      wildcard bins bit_7_rd_as_1 = {15'b??????1???????1};
	      wildcard bins bit_8_wr_as_0 = {15'b?????0????????0};
	      wildcard bins bit_8_wr_as_1 = {15'b?????1????????0};
	      wildcard bins bit_8_rd_as_0 = {15'b?????0????????1};
	      wildcard bins bit_8_rd_as_1 = {15'b?????1????????1};
	      wildcard bins bit_9_wr_as_0 = {15'b????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {15'b????1?????????0};
	      wildcard bins bit_9_rd_as_0 = {15'b????0?????????1};
	      wildcard bins bit_9_rd_as_1 = {15'b????1?????????1};
	      wildcard bins bit_10_wr_as_0 = {15'b???0??????????0};
	      wildcard bins bit_10_wr_as_1 = {15'b???1??????????0};
	      wildcard bins bit_10_rd_as_0 = {15'b???0??????????1};
	      wildcard bins bit_10_rd_as_1 = {15'b???1??????????1};
	      wildcard bins bit_11_wr_as_0 = {15'b??0???????????0};
	      wildcard bins bit_11_wr_as_1 = {15'b??1???????????0};
	      wildcard bins bit_11_rd_as_0 = {15'b??0???????????1};
	      wildcard bins bit_11_rd_as_1 = {15'b??1???????????1};
	      wildcard bins bit_12_wr_as_0 = {15'b?0????????????0};
	      wildcard bins bit_12_wr_as_1 = {15'b?1????????????0};
	      wildcard bins bit_12_rd_as_0 = {15'b?0????????????1};
	      wildcard bins bit_12_rd_as_1 = {15'b?1????????????1};
	      wildcard bins bit_13_wr_as_0 = {15'b0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {15'b1?????????????0};
	      wildcard bins bit_13_rd_as_0 = {15'b0?????????????1};
	      wildcard bins bit_13_rd_as_1 = {15'b1?????????????1};
	      option.weight = 56;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AsyncAcTxData");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AsyncAcTxData = uvm_reg_field::type_id::create("AsyncAcTxData",,get_full_name());
      this.AsyncAcTxData.configure(this, 14, 0, "RW", 0, 14'h2800, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcTxData)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcTxData


class ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcRxData extends uvm_reg;
	uvm_reg_field AsyncAcRxData;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AsyncAcRxData: coverpoint {m_data[13:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {15'b?????????????00};
	      wildcard bins bit_0_wr_as_1 = {15'b?????????????10};
	      wildcard bins bit_0_rd = {15'b??????????????1};
	      wildcard bins bit_1_wr_as_0 = {15'b????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {15'b????????????1?0};
	      wildcard bins bit_1_rd = {15'b??????????????1};
	      wildcard bins bit_2_wr_as_0 = {15'b???????????0??0};
	      wildcard bins bit_2_wr_as_1 = {15'b???????????1??0};
	      wildcard bins bit_2_rd = {15'b??????????????1};
	      wildcard bins bit_3_wr_as_0 = {15'b??????????0???0};
	      wildcard bins bit_3_wr_as_1 = {15'b??????????1???0};
	      wildcard bins bit_3_rd = {15'b??????????????1};
	      wildcard bins bit_4_wr_as_0 = {15'b?????????0????0};
	      wildcard bins bit_4_wr_as_1 = {15'b?????????1????0};
	      wildcard bins bit_4_rd = {15'b??????????????1};
	      wildcard bins bit_5_wr_as_0 = {15'b????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {15'b????????1?????0};
	      wildcard bins bit_5_rd = {15'b??????????????1};
	      wildcard bins bit_6_wr_as_0 = {15'b???????0??????0};
	      wildcard bins bit_6_wr_as_1 = {15'b???????1??????0};
	      wildcard bins bit_6_rd = {15'b??????????????1};
	      wildcard bins bit_7_wr_as_0 = {15'b??????0???????0};
	      wildcard bins bit_7_wr_as_1 = {15'b??????1???????0};
	      wildcard bins bit_7_rd = {15'b??????????????1};
	      wildcard bins bit_8_wr_as_0 = {15'b?????0????????0};
	      wildcard bins bit_8_wr_as_1 = {15'b?????1????????0};
	      wildcard bins bit_8_rd = {15'b??????????????1};
	      wildcard bins bit_9_wr_as_0 = {15'b????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {15'b????1?????????0};
	      wildcard bins bit_9_rd = {15'b??????????????1};
	      wildcard bins bit_10_wr_as_0 = {15'b???0??????????0};
	      wildcard bins bit_10_wr_as_1 = {15'b???1??????????0};
	      wildcard bins bit_10_rd = {15'b??????????????1};
	      wildcard bins bit_11_wr_as_0 = {15'b??0???????????0};
	      wildcard bins bit_11_wr_as_1 = {15'b??1???????????0};
	      wildcard bins bit_11_rd = {15'b??????????????1};
	      wildcard bins bit_12_wr_as_0 = {15'b?0????????????0};
	      wildcard bins bit_12_wr_as_1 = {15'b?1????????????0};
	      wildcard bins bit_12_rd = {15'b??????????????1};
	      wildcard bins bit_13_wr_as_0 = {15'b0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {15'b1?????????????0};
	      wildcard bins bit_13_rd = {15'b??????????????1};
	      option.weight = 42;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AsyncAcRxData");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AsyncAcRxData = uvm_reg_field::type_id::create("AsyncAcRxData",,get_full_name());
      this.AsyncAcRxData.configure(this, 14, 0, "RO", 1, 14'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcRxData)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcRxData


class ral_reg_DWC_DDRPHYA_AC1_p0_ForceClkDisable extends uvm_reg;
	rand uvm_reg_field ForceClkDisable;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ForceClkDisable: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_ForceClkDisable");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ForceClkDisable = uvm_reg_field::type_id::create("ForceClkDisable",,get_full_name());
      this.ForceClkDisable.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ForceClkDisable)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ForceClkDisable


class ral_reg_DWC_DDRPHYA_AC1_p0_CaBusTriEn extends uvm_reg;
	rand uvm_reg_field CaBusTriEn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CaBusTriEn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_CaBusTriEn");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CaBusTriEn = uvm_reg_field::type_id::create("CaBusTriEn",,get_full_name());
      this.CaBusTriEn.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_CaBusTriEn)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_CaBusTriEn


class ral_reg_DWC_DDRPHYA_AC1_p0_AcLnDisable extends uvm_reg;
	rand uvm_reg_field AcLnDisable;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcLnDisable: coverpoint {m_data[12:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {14'b????????????00};
	      wildcard bins bit_0_wr_as_1 = {14'b????????????10};
	      wildcard bins bit_0_rd_as_0 = {14'b????????????01};
	      wildcard bins bit_0_rd_as_1 = {14'b????????????11};
	      wildcard bins bit_1_wr_as_0 = {14'b???????????0?0};
	      wildcard bins bit_1_wr_as_1 = {14'b???????????1?0};
	      wildcard bins bit_1_rd_as_0 = {14'b???????????0?1};
	      wildcard bins bit_1_rd_as_1 = {14'b???????????1?1};
	      wildcard bins bit_2_wr_as_0 = {14'b??????????0??0};
	      wildcard bins bit_2_wr_as_1 = {14'b??????????1??0};
	      wildcard bins bit_2_rd_as_0 = {14'b??????????0??1};
	      wildcard bins bit_2_rd_as_1 = {14'b??????????1??1};
	      wildcard bins bit_3_wr_as_0 = {14'b?????????0???0};
	      wildcard bins bit_3_wr_as_1 = {14'b?????????1???0};
	      wildcard bins bit_3_rd_as_0 = {14'b?????????0???1};
	      wildcard bins bit_3_rd_as_1 = {14'b?????????1???1};
	      wildcard bins bit_4_wr_as_0 = {14'b????????0????0};
	      wildcard bins bit_4_wr_as_1 = {14'b????????1????0};
	      wildcard bins bit_4_rd_as_0 = {14'b????????0????1};
	      wildcard bins bit_4_rd_as_1 = {14'b????????1????1};
	      wildcard bins bit_5_wr_as_0 = {14'b???????0?????0};
	      wildcard bins bit_5_wr_as_1 = {14'b???????1?????0};
	      wildcard bins bit_5_rd_as_0 = {14'b???????0?????1};
	      wildcard bins bit_5_rd_as_1 = {14'b???????1?????1};
	      wildcard bins bit_6_wr_as_0 = {14'b??????0??????0};
	      wildcard bins bit_6_wr_as_1 = {14'b??????1??????0};
	      wildcard bins bit_6_rd_as_0 = {14'b??????0??????1};
	      wildcard bins bit_6_rd_as_1 = {14'b??????1??????1};
	      wildcard bins bit_7_wr_as_0 = {14'b?????0???????0};
	      wildcard bins bit_7_wr_as_1 = {14'b?????1???????0};
	      wildcard bins bit_7_rd_as_0 = {14'b?????0???????1};
	      wildcard bins bit_7_rd_as_1 = {14'b?????1???????1};
	      wildcard bins bit_8_wr_as_0 = {14'b????0????????0};
	      wildcard bins bit_8_wr_as_1 = {14'b????1????????0};
	      wildcard bins bit_8_rd_as_0 = {14'b????0????????1};
	      wildcard bins bit_8_rd_as_1 = {14'b????1????????1};
	      wildcard bins bit_9_wr_as_0 = {14'b???0?????????0};
	      wildcard bins bit_9_wr_as_1 = {14'b???1?????????0};
	      wildcard bins bit_9_rd_as_0 = {14'b???0?????????1};
	      wildcard bins bit_9_rd_as_1 = {14'b???1?????????1};
	      wildcard bins bit_10_wr_as_0 = {14'b??0??????????0};
	      wildcard bins bit_10_wr_as_1 = {14'b??1??????????0};
	      wildcard bins bit_10_rd_as_0 = {14'b??0??????????1};
	      wildcard bins bit_10_rd_as_1 = {14'b??1??????????1};
	      wildcard bins bit_11_wr_as_0 = {14'b?0???????????0};
	      wildcard bins bit_11_wr_as_1 = {14'b?1???????????0};
	      wildcard bins bit_11_rd_as_0 = {14'b?0???????????1};
	      wildcard bins bit_11_rd_as_1 = {14'b?1???????????1};
	      wildcard bins bit_12_wr_as_0 = {14'b0????????????0};
	      wildcard bins bit_12_wr_as_1 = {14'b1????????????0};
	      wildcard bins bit_12_rd_as_0 = {14'b0????????????1};
	      wildcard bins bit_12_rd_as_1 = {14'b1????????????1};
	      option.weight = 52;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcLnDisable");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcLnDisable = uvm_reg_field::type_id::create("AcLnDisable",,get_full_name());
      this.AcLnDisable.configure(this, 13, 0, "RW", 0, 13'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcLnDisable)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcLnDisable


class ral_reg_DWC_DDRPHYA_AC1_p0_DfiClkAcLnDis extends uvm_reg;
	rand uvm_reg_field DfiClkAcLnDis;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiClkAcLnDis: coverpoint {m_data[12:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {14'b????????????00};
	      wildcard bins bit_0_wr_as_1 = {14'b????????????10};
	      wildcard bins bit_0_rd_as_0 = {14'b????????????01};
	      wildcard bins bit_0_rd_as_1 = {14'b????????????11};
	      wildcard bins bit_1_wr_as_0 = {14'b???????????0?0};
	      wildcard bins bit_1_wr_as_1 = {14'b???????????1?0};
	      wildcard bins bit_1_rd_as_0 = {14'b???????????0?1};
	      wildcard bins bit_1_rd_as_1 = {14'b???????????1?1};
	      wildcard bins bit_2_wr_as_0 = {14'b??????????0??0};
	      wildcard bins bit_2_wr_as_1 = {14'b??????????1??0};
	      wildcard bins bit_2_rd_as_0 = {14'b??????????0??1};
	      wildcard bins bit_2_rd_as_1 = {14'b??????????1??1};
	      wildcard bins bit_3_wr_as_0 = {14'b?????????0???0};
	      wildcard bins bit_3_wr_as_1 = {14'b?????????1???0};
	      wildcard bins bit_3_rd_as_0 = {14'b?????????0???1};
	      wildcard bins bit_3_rd_as_1 = {14'b?????????1???1};
	      wildcard bins bit_4_wr_as_0 = {14'b????????0????0};
	      wildcard bins bit_4_wr_as_1 = {14'b????????1????0};
	      wildcard bins bit_4_rd_as_0 = {14'b????????0????1};
	      wildcard bins bit_4_rd_as_1 = {14'b????????1????1};
	      wildcard bins bit_5_wr_as_0 = {14'b???????0?????0};
	      wildcard bins bit_5_wr_as_1 = {14'b???????1?????0};
	      wildcard bins bit_5_rd_as_0 = {14'b???????0?????1};
	      wildcard bins bit_5_rd_as_1 = {14'b???????1?????1};
	      wildcard bins bit_6_wr_as_0 = {14'b??????0??????0};
	      wildcard bins bit_6_wr_as_1 = {14'b??????1??????0};
	      wildcard bins bit_6_rd_as_0 = {14'b??????0??????1};
	      wildcard bins bit_6_rd_as_1 = {14'b??????1??????1};
	      wildcard bins bit_7_wr_as_0 = {14'b?????0???????0};
	      wildcard bins bit_7_wr_as_1 = {14'b?????1???????0};
	      wildcard bins bit_7_rd_as_0 = {14'b?????0???????1};
	      wildcard bins bit_7_rd_as_1 = {14'b?????1???????1};
	      wildcard bins bit_8_wr_as_0 = {14'b????0????????0};
	      wildcard bins bit_8_wr_as_1 = {14'b????1????????0};
	      wildcard bins bit_8_rd_as_0 = {14'b????0????????1};
	      wildcard bins bit_8_rd_as_1 = {14'b????1????????1};
	      wildcard bins bit_9_wr_as_0 = {14'b???0?????????0};
	      wildcard bins bit_9_wr_as_1 = {14'b???1?????????0};
	      wildcard bins bit_9_rd_as_0 = {14'b???0?????????1};
	      wildcard bins bit_9_rd_as_1 = {14'b???1?????????1};
	      wildcard bins bit_10_wr_as_0 = {14'b??0??????????0};
	      wildcard bins bit_10_wr_as_1 = {14'b??1??????????0};
	      wildcard bins bit_10_rd_as_0 = {14'b??0??????????1};
	      wildcard bins bit_10_rd_as_1 = {14'b??1??????????1};
	      wildcard bins bit_11_wr_as_0 = {14'b?0???????????0};
	      wildcard bins bit_11_wr_as_1 = {14'b?1???????????0};
	      wildcard bins bit_11_rd_as_0 = {14'b?0???????????1};
	      wildcard bins bit_11_rd_as_1 = {14'b?1???????????1};
	      wildcard bins bit_12_wr_as_0 = {14'b0????????????0};
	      wildcard bins bit_12_wr_as_1 = {14'b1????????????0};
	      wildcard bins bit_12_rd_as_0 = {14'b0????????????1};
	      wildcard bins bit_12_rd_as_1 = {14'b1????????????1};
	      option.weight = 52;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_DfiClkAcLnDis");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiClkAcLnDis = uvm_reg_field::type_id::create("DfiClkAcLnDis",,get_full_name());
      this.DfiClkAcLnDis.configure(this, 13, 0, "RW", 0, 13'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_DfiClkAcLnDis)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_DfiClkAcLnDis


class ral_reg_DWC_DDRPHYA_AC1_p0_PClkAcLnDis extends uvm_reg;
	rand uvm_reg_field PClkAcLnDis;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PClkAcLnDis: coverpoint {m_data[12:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {14'b????????????00};
	      wildcard bins bit_0_wr_as_1 = {14'b????????????10};
	      wildcard bins bit_0_rd_as_0 = {14'b????????????01};
	      wildcard bins bit_0_rd_as_1 = {14'b????????????11};
	      wildcard bins bit_1_wr_as_0 = {14'b???????????0?0};
	      wildcard bins bit_1_wr_as_1 = {14'b???????????1?0};
	      wildcard bins bit_1_rd_as_0 = {14'b???????????0?1};
	      wildcard bins bit_1_rd_as_1 = {14'b???????????1?1};
	      wildcard bins bit_2_wr_as_0 = {14'b??????????0??0};
	      wildcard bins bit_2_wr_as_1 = {14'b??????????1??0};
	      wildcard bins bit_2_rd_as_0 = {14'b??????????0??1};
	      wildcard bins bit_2_rd_as_1 = {14'b??????????1??1};
	      wildcard bins bit_3_wr_as_0 = {14'b?????????0???0};
	      wildcard bins bit_3_wr_as_1 = {14'b?????????1???0};
	      wildcard bins bit_3_rd_as_0 = {14'b?????????0???1};
	      wildcard bins bit_3_rd_as_1 = {14'b?????????1???1};
	      wildcard bins bit_4_wr_as_0 = {14'b????????0????0};
	      wildcard bins bit_4_wr_as_1 = {14'b????????1????0};
	      wildcard bins bit_4_rd_as_0 = {14'b????????0????1};
	      wildcard bins bit_4_rd_as_1 = {14'b????????1????1};
	      wildcard bins bit_5_wr_as_0 = {14'b???????0?????0};
	      wildcard bins bit_5_wr_as_1 = {14'b???????1?????0};
	      wildcard bins bit_5_rd_as_0 = {14'b???????0?????1};
	      wildcard bins bit_5_rd_as_1 = {14'b???????1?????1};
	      wildcard bins bit_6_wr_as_0 = {14'b??????0??????0};
	      wildcard bins bit_6_wr_as_1 = {14'b??????1??????0};
	      wildcard bins bit_6_rd_as_0 = {14'b??????0??????1};
	      wildcard bins bit_6_rd_as_1 = {14'b??????1??????1};
	      wildcard bins bit_7_wr_as_0 = {14'b?????0???????0};
	      wildcard bins bit_7_wr_as_1 = {14'b?????1???????0};
	      wildcard bins bit_7_rd_as_0 = {14'b?????0???????1};
	      wildcard bins bit_7_rd_as_1 = {14'b?????1???????1};
	      wildcard bins bit_8_wr_as_0 = {14'b????0????????0};
	      wildcard bins bit_8_wr_as_1 = {14'b????1????????0};
	      wildcard bins bit_8_rd_as_0 = {14'b????0????????1};
	      wildcard bins bit_8_rd_as_1 = {14'b????1????????1};
	      wildcard bins bit_9_wr_as_0 = {14'b???0?????????0};
	      wildcard bins bit_9_wr_as_1 = {14'b???1?????????0};
	      wildcard bins bit_9_rd_as_0 = {14'b???0?????????1};
	      wildcard bins bit_9_rd_as_1 = {14'b???1?????????1};
	      wildcard bins bit_10_wr_as_0 = {14'b??0??????????0};
	      wildcard bins bit_10_wr_as_1 = {14'b??1??????????0};
	      wildcard bins bit_10_rd_as_0 = {14'b??0??????????1};
	      wildcard bins bit_10_rd_as_1 = {14'b??1??????????1};
	      wildcard bins bit_11_wr_as_0 = {14'b?0???????????0};
	      wildcard bins bit_11_wr_as_1 = {14'b?1???????????0};
	      wildcard bins bit_11_rd_as_0 = {14'b?0???????????1};
	      wildcard bins bit_11_rd_as_1 = {14'b?1???????????1};
	      wildcard bins bit_12_wr_as_0 = {14'b0????????????0};
	      wildcard bins bit_12_wr_as_1 = {14'b1????????????0};
	      wildcard bins bit_12_rd_as_0 = {14'b0????????????1};
	      wildcard bins bit_12_rd_as_1 = {14'b1????????????1};
	      option.weight = 52;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_PClkAcLnDis");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PClkAcLnDis = uvm_reg_field::type_id::create("PClkAcLnDis",,get_full_name());
      this.PClkAcLnDis.configure(this, 13, 0, "RW", 0, 13'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_PClkAcLnDis)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_PClkAcLnDis


class ral_reg_DWC_DDRPHYA_AC1_p0_AcLcdlCalPhDetOut extends uvm_reg;
	uvm_reg_field AcLcdlCalPhDetOut;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcLcdlCalPhDetOut: coverpoint {m_data[11:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcLcdlCalPhDetOut");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcLcdlCalPhDetOut = uvm_reg_field::type_id::create("AcLcdlCalPhDetOut",,get_full_name());
      this.AcLcdlCalPhDetOut.configure(this, 12, 0, "RO", 1, 12'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcLcdlCalPhDetOut)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcLcdlCalPhDetOut


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r0_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDly_r0_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly_r0_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDly_r0_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly_r0_p0 = uvm_reg_field::type_id::create("ACXTxDly_r0_p0",,get_full_name());
      this.ACXTxDly_r0_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r0_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r0_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_CKXTxDly_p0 extends uvm_reg;
	rand uvm_reg_field CKXTxDly_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CKXTxDly_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_CKXTxDly_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CKXTxDly_p0 = uvm_reg_field::type_id::create("CKXTxDly_p0",,get_full_name());
      this.CKXTxDly_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_CKXTxDly_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_CKXTxDly_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDlyDTO_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDlyDTO_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDlyDTO_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDlyDTO_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDlyDTO_p0 = uvm_reg_field::type_id::create("ACXTxDlyDTO_p0",,get_full_name());
      this.ACXTxDlyDTO_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDlyDTO_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDlyDTO_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r0_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDly2nMode_r0_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly2nMode_r0_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r0_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly2nMode_r0_p0 = uvm_reg_field::type_id::create("ACXTxDly2nMode_r0_p0",,get_full_name());
      this.ACXTxDly2nMode_r0_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r0_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r0_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_AcLcdlUpdInterval_p0 extends uvm_reg;
	rand uvm_reg_field AcLcdlUpdInterval_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcLcdlUpdInterval_p0: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcLcdlUpdInterval_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcLcdlUpdInterval_p0 = uvm_reg_field::type_id::create("AcLcdlUpdInterval_p0",,get_full_name());
      this.AcLcdlUpdInterval_p0.configure(this, 16, 0, "RW", 0, 16'h80, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcLcdlUpdInterval_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcLcdlUpdInterval_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_LcdlCalSeqUpdCK_p0 extends uvm_reg;
	rand uvm_reg_field LcdlCalSeqUpdCK_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   LcdlCalSeqUpdCK_p0: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_LcdlCalSeqUpdCK_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.LcdlCalSeqUpdCK_p0 = uvm_reg_field::type_id::create("LcdlCalSeqUpdCK_p0",,get_full_name());
      this.LcdlCalSeqUpdCK_p0.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_LcdlCalSeqUpdCK_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_LcdlCalSeqUpdCK_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_CkTriEn extends uvm_reg;
	rand uvm_reg_field CkTriEn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CkTriEn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_CkTriEn");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CkTriEn = uvm_reg_field::type_id::create("CkTriEn",,get_full_name());
      this.CkTriEn.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_CkTriEn)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_CkTriEn


class ral_reg_DWC_DDRPHYA_AC1_p0_ACReserved0 extends uvm_reg;
	rand uvm_reg_field ACReserved0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACReserved0: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACReserved0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACReserved0 = uvm_reg_field::type_id::create("ACReserved0",,get_full_name());
      this.ACReserved0.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACReserved0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACReserved0


class ral_reg_DWC_DDRPHYA_AC1_p0_LcdlCalCtrl extends uvm_reg;
	rand uvm_reg_field LcdlCalCtrl;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   LcdlCalCtrl: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_LcdlCalCtrl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.LcdlCalCtrl = uvm_reg_field::type_id::create("LcdlCalCtrl",,get_full_name());
      this.LcdlCalCtrl.configure(this, 6, 0, "RW", 0, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_LcdlCalCtrl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_LcdlCalCtrl


class ral_reg_DWC_DDRPHYA_AC1_p0_PUBReservedP1_p0 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_PUBReservedP1_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PUBReservedP1_p0 = uvm_reg_field::type_id::create("PUBReservedP1_p0",,get_full_name());
      this.PUBReservedP1_p0.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_PUBReservedP1_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_PUBReservedP1_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCDCtrl_p0 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_PclkDCDCtrl_p0");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCDCtrl_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCDCtrl_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_ForceInternalUpdate extends uvm_reg;
	rand uvm_reg_field ForceInternalUpdate;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ForceInternalUpdate: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_ForceInternalUpdate");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ForceInternalUpdate = uvm_reg_field::type_id::create("ForceInternalUpdate",,get_full_name());
      this.ForceInternalUpdate.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ForceInternalUpdate)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ForceInternalUpdate


class ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSEC0 extends uvm_reg;
	uvm_reg_field ATestPrbsErrCntSEC0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ATestPrbsErrCntSEC0: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSEC0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ATestPrbsErrCntSEC0 = uvm_reg_field::type_id::create("ATestPrbsErrCntSEC0",,get_full_name());
      this.ATestPrbsErrCntSEC0.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSEC0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSEC0


class ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSEC1 extends uvm_reg;
	uvm_reg_field ATestPrbsErrCntSEC1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ATestPrbsErrCntSEC1: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSEC1");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ATestPrbsErrCntSEC1 = uvm_reg_field::type_id::create("ATestPrbsErrCntSEC1",,get_full_name());
      this.ATestPrbsErrCntSEC1.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSEC1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSEC1


class ral_reg_DWC_DDRPHYA_AC1_p0_AcPDsampleSEC0 extends uvm_reg;
	uvm_reg_field AcPDsampleSEC0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcPDsampleSEC0: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcPDsampleSEC0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcPDsampleSEC0 = uvm_reg_field::type_id::create("AcPDsampleSEC0",,get_full_name());
      this.AcPDsampleSEC0.configure(this, 1, 0, "RO", 1, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcPDsampleSEC0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcPDsampleSEC0


class ral_reg_DWC_DDRPHYA_AC1_p0_AcPDsampleSEC1 extends uvm_reg;
	uvm_reg_field AcPDsampleSEC1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcPDsampleSEC1: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcPDsampleSEC1");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcPDsampleSEC1 = uvm_reg_field::type_id::create("AcPDsampleSEC1",,get_full_name());
      this.AcPDsampleSEC1.configure(this, 1, 0, "RO", 1, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcPDsampleSEC1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcPDsampleSEC1


class ral_reg_DWC_DDRPHYA_AC1_p0_AcPDsampleDIFF extends uvm_reg;
	uvm_reg_field PDsampleT;
	uvm_reg_field PDsampleC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PDsampleT: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   PDsampleC: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcPDsampleDIFF");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PDsampleT = uvm_reg_field::type_id::create("PDsampleT",,get_full_name());
      this.PDsampleT.configure(this, 1, 0, "RO", 1, 1'h0, 1, 0, 0);
      this.PDsampleC = uvm_reg_field::type_id::create("PDsampleC",,get_full_name());
      this.PDsampleC.configure(this, 1, 1, "RO", 1, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcPDsampleDIFF)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcPDsampleDIFF


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r1_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDly_r1_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly_r1_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDly_r1_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly_r1_p0 = uvm_reg_field::type_id::create("ACXTxDly_r1_p0",,get_full_name());
      this.ACXTxDly_r1_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r1_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r1_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r1_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDly2nMode_r1_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly2nMode_r1_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r1_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly2nMode_r1_p0 = uvm_reg_field::type_id::create("ACXTxDly2nMode_r1_p0",,get_full_name());
      this.ACXTxDly2nMode_r1_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r1_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r1_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r2_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDly_r2_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly_r2_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDly_r2_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly_r2_p0 = uvm_reg_field::type_id::create("ACXTxDly_r2_p0",,get_full_name());
      this.ACXTxDly_r2_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r2_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r2_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r2_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDly2nMode_r2_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly2nMode_r2_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r2_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly2nMode_r2_p0 = uvm_reg_field::type_id::create("ACXTxDly2nMode_r2_p0",,get_full_name());
      this.ACXTxDly2nMode_r2_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r2_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r2_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r3_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDly_r3_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly_r3_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDly_r3_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly_r3_p0 = uvm_reg_field::type_id::create("ACXTxDly_r3_p0",,get_full_name());
      this.ACXTxDly_r3_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r3_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r3_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r3_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDly2nMode_r3_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly2nMode_r3_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r3_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly2nMode_r3_p0 = uvm_reg_field::type_id::create("ACXTxDly2nMode_r3_p0",,get_full_name());
      this.ACXTxDly2nMode_r3_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r3_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r3_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntDIFF0T extends uvm_reg;
	uvm_reg_field ATestPrbsErrCntDIFF0T;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ATestPrbsErrCntDIFF0T: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntDIFF0T");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ATestPrbsErrCntDIFF0T = uvm_reg_field::type_id::create("ATestPrbsErrCntDIFF0T",,get_full_name());
      this.ATestPrbsErrCntDIFF0T.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntDIFF0T)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntDIFF0T


class ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntDIFF0C extends uvm_reg;
	uvm_reg_field ATestPrbsErrCntDIFF0C;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ATestPrbsErrCntDIFF0C: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntDIFF0C");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ATestPrbsErrCntDIFF0C = uvm_reg_field::type_id::create("ATestPrbsErrCntDIFF0C",,get_full_name());
      this.ATestPrbsErrCntDIFF0C.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntDIFF0C)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntDIFF0C


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r4_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDly_r4_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly_r4_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDly_r4_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly_r4_p0 = uvm_reg_field::type_id::create("ACXTxDly_r4_p0",,get_full_name());
      this.ACXTxDly_r4_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r4_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r4_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r4_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDly2nMode_r4_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly2nMode_r4_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r4_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly2nMode_r4_p0 = uvm_reg_field::type_id::create("ACXTxDly2nMode_r4_p0",,get_full_name());
      this.ACXTxDly2nMode_r4_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r4_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r4_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r5_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDly_r5_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly_r5_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDly_r5_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly_r5_p0 = uvm_reg_field::type_id::create("ACXTxDly_r5_p0",,get_full_name());
      this.ACXTxDly_r5_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r5_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r5_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r5_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDly2nMode_r5_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly2nMode_r5_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r5_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly2nMode_r5_p0 = uvm_reg_field::type_id::create("ACXTxDly2nMode_r5_p0",,get_full_name());
      this.ACXTxDly2nMode_r5_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r5_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r5_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r6_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDly_r6_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly_r6_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDly_r6_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly_r6_p0 = uvm_reg_field::type_id::create("ACXTxDly_r6_p0",,get_full_name());
      this.ACXTxDly_r6_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r6_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r6_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r6_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDly2nMode_r6_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly2nMode_r6_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r6_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly2nMode_r6_p0 = uvm_reg_field::type_id::create("ACXTxDly2nMode_r6_p0",,get_full_name());
      this.ACXTxDly2nMode_r6_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r6_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r6_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r7_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDly_r7_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly_r7_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDly_r7_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly_r7_p0 = uvm_reg_field::type_id::create("ACXTxDly_r7_p0",,get_full_name());
      this.ACXTxDly_r7_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r7_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r7_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r7_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDly2nMode_r7_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly2nMode_r7_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r7_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly2nMode_r7_p0 = uvm_reg_field::type_id::create("ACXTxDly2nMode_r7_p0",,get_full_name());
      this.ACXTxDly2nMode_r7_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r7_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r7_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCACalCtrl0AC extends uvm_reg;
	rand uvm_reg_field PclkDCAIncOnHiAC;
	rand uvm_reg_field PclkDCAIncOnLoAC;
	rand uvm_reg_field PclkDCADecOnHiAC;
	rand uvm_reg_field PclkDCADecOnLoAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCAIncOnHiAC: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PclkDCAIncOnLoAC: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PclkDCADecOnHiAC: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PclkDCADecOnLoAC: coverpoint {m_data[3:3], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_PclkDCACalCtrl0AC");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCAIncOnHiAC = uvm_reg_field::type_id::create("PclkDCAIncOnHiAC",,get_full_name());
      this.PclkDCAIncOnHiAC.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 0);
      this.PclkDCAIncOnLoAC = uvm_reg_field::type_id::create("PclkDCAIncOnLoAC",,get_full_name());
      this.PclkDCAIncOnLoAC.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.PclkDCADecOnHiAC = uvm_reg_field::type_id::create("PclkDCADecOnHiAC",,get_full_name());
      this.PclkDCADecOnHiAC.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
      this.PclkDCADecOnLoAC = uvm_reg_field::type_id::create("PclkDCADecOnLoAC",,get_full_name());
      this.PclkDCADecOnLoAC.configure(this, 1, 3, "RW", 0, 1'h1, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCACalCtrl0AC)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCACalCtrl0AC


class ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCADynCtrl extends uvm_reg;
	rand uvm_reg_field PclkDCACalReset;
	rand uvm_reg_field PclkDCAQuickSearch;
	rand uvm_reg_field PclkDCAForceSampVld;
	rand uvm_reg_field PclkDCAForceUpd;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACalReset: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PclkDCAQuickSearch: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PclkDCAForceSampVld: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   PclkDCAForceUpd: coverpoint {m_data[3:3], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_PclkDCADynCtrl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACalReset = uvm_reg_field::type_id::create("PclkDCACalReset",,get_full_name());
      this.PclkDCACalReset.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 0);
      this.PclkDCAQuickSearch = uvm_reg_field::type_id::create("PclkDCAQuickSearch",,get_full_name());
      this.PclkDCAQuickSearch.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.PclkDCAForceSampVld = uvm_reg_field::type_id::create("PclkDCAForceSampVld",,get_full_name());
      this.PclkDCAForceSampVld.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
      this.PclkDCAForceUpd = uvm_reg_field::type_id::create("PclkDCAForceUpd",,get_full_name());
      this.PclkDCAForceUpd.configure(this, 1, 3, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCADynCtrl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCADynCtrl


class ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCAStaticCtrl0AC_p0 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_PclkDCAStaticCtrl0AC_p0");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCAStaticCtrl0AC_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCAStaticCtrl0AC_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCASampCntAC extends uvm_reg;
	rand uvm_reg_field PclkDCAQkSampCntAC;
	rand uvm_reg_field PclkDCAFineSampCntAAC;
	rand uvm_reg_field PclkDCAFineSampCntBAC;
	rand uvm_reg_field PclkDCACoarseSampCntAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCAQkSampCntAC: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   PclkDCAFineSampCntAAC: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   PclkDCAFineSampCntBAC: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   PclkDCACoarseSampCntAC: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_PclkDCASampCntAC");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCAQkSampCntAC = uvm_reg_field::type_id::create("PclkDCAQkSampCntAC",,get_full_name());
      this.PclkDCAQkSampCntAC.configure(this, 4, 0, "RW", 0, 4'h3, 1, 0, 0);
      this.PclkDCAFineSampCntAAC = uvm_reg_field::type_id::create("PclkDCAFineSampCntAAC",,get_full_name());
      this.PclkDCAFineSampCntAAC.configure(this, 4, 4, "RW", 0, 4'h6, 1, 0, 0);
      this.PclkDCAFineSampCntBAC = uvm_reg_field::type_id::create("PclkDCAFineSampCntBAC",,get_full_name());
      this.PclkDCAFineSampCntBAC.configure(this, 4, 8, "RW", 0, 4'h6, 1, 0, 0);
      this.PclkDCACoarseSampCntAC = uvm_reg_field::type_id::create("PclkDCACoarseSampCntAC",,get_full_name());
      this.PclkDCACoarseSampCntAC.configure(this, 4, 12, "RW", 0, 4'h4, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCASampCntAC)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCASampCntAC


class ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCAHysMaskAC extends uvm_reg;
	rand uvm_reg_field PclkDCAHysMaskAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCAHysMaskAC: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_PclkDCAHysMaskAC");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCAHysMaskAC = uvm_reg_field::type_id::create("PclkDCAHysMaskAC",,get_full_name());
      this.PclkDCAHysMaskAC.configure(this, 3, 0, "RW", 0, 3'h7, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCAHysMaskAC)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCAHysMaskAC


class ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCACalFineBoundAC extends uvm_reg;
	rand uvm_reg_field PclkDCAURMaxFineAC;
	rand uvm_reg_field PclkDCAURMinFineAC;
	rand uvm_reg_field PclkDCALLMaxFineAC;
	rand uvm_reg_field PclkDCALLMinFineAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCAURMaxFineAC: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	   PclkDCAURMinFineAC: coverpoint {m_data[5:3], m_is_read} iff(m_be) {
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
	   PclkDCALLMaxFineAC: coverpoint {m_data[8:6], m_is_read} iff(m_be) {
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
	   PclkDCALLMinFineAC: coverpoint {m_data[11:9], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_PclkDCACalFineBoundAC");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCAURMaxFineAC = uvm_reg_field::type_id::create("PclkDCAURMaxFineAC",,get_full_name());
      this.PclkDCAURMaxFineAC.configure(this, 3, 0, "RW", 0, 3'h6, 1, 0, 0);
      this.PclkDCAURMinFineAC = uvm_reg_field::type_id::create("PclkDCAURMinFineAC",,get_full_name());
      this.PclkDCAURMinFineAC.configure(this, 3, 3, "RW", 0, 3'h0, 1, 0, 0);
      this.PclkDCALLMaxFineAC = uvm_reg_field::type_id::create("PclkDCALLMaxFineAC",,get_full_name());
      this.PclkDCALLMaxFineAC.configure(this, 3, 6, "RW", 0, 3'h1, 1, 0, 0);
      this.PclkDCALLMinFineAC = uvm_reg_field::type_id::create("PclkDCALLMinFineAC",,get_full_name());
      this.PclkDCALLMinFineAC.configure(this, 3, 9, "RW", 0, 3'h6, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCACalFineBoundAC)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCACalFineBoundAC


class ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCANextFineOnCoarseAC extends uvm_reg;
	rand uvm_reg_field PclkDCACoarseIncFineURAC;
	rand uvm_reg_field PclkDCACoarseDecFineURAC;
	rand uvm_reg_field PclkDCACoarseIncFineLLAC;
	rand uvm_reg_field PclkDCACoarseDecFineLLAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACoarseIncFineURAC: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   PclkDCACoarseDecFineURAC: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   PclkDCACoarseIncFineLLAC: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   PclkDCACoarseDecFineLLAC: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_PclkDCANextFineOnCoarseAC");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACoarseIncFineURAC = uvm_reg_field::type_id::create("PclkDCACoarseIncFineURAC",,get_full_name());
      this.PclkDCACoarseIncFineURAC.configure(this, 4, 0, "RW", 0, 4'h4, 1, 0, 0);
      this.PclkDCACoarseDecFineURAC = uvm_reg_field::type_id::create("PclkDCACoarseDecFineURAC",,get_full_name());
      this.PclkDCACoarseDecFineURAC.configure(this, 4, 4, "RW", 0, 4'h2, 1, 0, 0);
      this.PclkDCACoarseIncFineLLAC = uvm_reg_field::type_id::create("PclkDCACoarseIncFineLLAC",,get_full_name());
      this.PclkDCACoarseIncFineLLAC.configure(this, 4, 8, "RW", 0, 4'ha, 1, 0, 0);
      this.PclkDCACoarseDecFineLLAC = uvm_reg_field::type_id::create("PclkDCACoarseDecFineLLAC",,get_full_name());
      this.PclkDCACoarseDecFineLLAC.configure(this, 4, 12, "RW", 0, 4'hc, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCANextFineOnCoarseAC)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCANextFineOnCoarseAC


class ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCAFullSearchIVACAC extends uvm_reg;
	rand uvm_reg_field PclkDCAFineIVMaxAC;
	rand uvm_reg_field PclkDCAFineIVMinAC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCAFineIVMaxAC: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   PclkDCAFineIVMinAC: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_PclkDCAFullSearchIVACAC");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCAFineIVMaxAC = uvm_reg_field::type_id::create("PclkDCAFineIVMaxAC",,get_full_name());
      this.PclkDCAFineIVMaxAC.configure(this, 4, 0, "RW", 0, 4'h6, 1, 0, 0);
      this.PclkDCAFineIVMinAC = uvm_reg_field::type_id::create("PclkDCAFineIVMinAC",,get_full_name());
      this.PclkDCAFineIVMinAC.configure(this, 4, 4, "RW", 0, 4'he, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCAFullSearchIVACAC)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCAFullSearchIVACAC


class ral_reg_DWC_DDRPHYA_AC1_p0_LcdlTstCtrl extends uvm_reg;
	rand uvm_reg_field LcdlTstCtrl;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   LcdlTstCtrl: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_LcdlTstCtrl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.LcdlTstCtrl = uvm_reg_field::type_id::create("LcdlTstCtrl",,get_full_name());
      this.LcdlTstCtrl.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_LcdlTstCtrl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_LcdlTstCtrl


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r8_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDly_r8_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly_r8_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDly_r8_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly_r8_p0 = uvm_reg_field::type_id::create("ACXTxDly_r8_p0",,get_full_name());
      this.ACXTxDly_r8_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r8_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r8_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r8_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDly2nMode_r8_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly2nMode_r8_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r8_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly2nMode_r8_p0 = uvm_reg_field::type_id::create("ACXTxDly2nMode_r8_p0",,get_full_name());
      this.ACXTxDly2nMode_r8_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r8_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r8_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn0 extends uvm_reg;
	rand uvm_reg_field AcLoopBackEnLn0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcLoopBackEnLn0: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcLoopBackEnLn0 = uvm_reg_field::type_id::create("AcLoopBackEnLn0",,get_full_name());
      this.AcLoopBackEnLn0.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn0


class ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn1 extends uvm_reg;
	rand uvm_reg_field AcLoopBackEnLn1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcLoopBackEnLn1: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn1");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcLoopBackEnLn1 = uvm_reg_field::type_id::create("AcLoopBackEnLn1",,get_full_name());
      this.AcLoopBackEnLn1.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn1


class ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn2 extends uvm_reg;
	rand uvm_reg_field AcLoopBackEnLn2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcLoopBackEnLn2: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcLoopBackEnLn2 = uvm_reg_field::type_id::create("AcLoopBackEnLn2",,get_full_name());
      this.AcLoopBackEnLn2.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn2


class ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn3 extends uvm_reg;
	rand uvm_reg_field AcLoopBackEnLn3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcLoopBackEnLn3: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn3");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcLoopBackEnLn3 = uvm_reg_field::type_id::create("AcLoopBackEnLn3",,get_full_name());
      this.AcLoopBackEnLn3.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn3


class ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn4 extends uvm_reg;
	rand uvm_reg_field AcLoopBackEnLn4;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcLoopBackEnLn4: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn4");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcLoopBackEnLn4 = uvm_reg_field::type_id::create("AcLoopBackEnLn4",,get_full_name());
      this.AcLoopBackEnLn4.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn4)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn4


class ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn5 extends uvm_reg;
	rand uvm_reg_field AcLoopBackEnLn5;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcLoopBackEnLn5: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn5");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcLoopBackEnLn5 = uvm_reg_field::type_id::create("AcLoopBackEnLn5",,get_full_name());
      this.AcLoopBackEnLn5.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn5)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn5


class ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn6 extends uvm_reg;
	rand uvm_reg_field AcLoopBackEnLn6;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcLoopBackEnLn6: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn6");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcLoopBackEnLn6 = uvm_reg_field::type_id::create("AcLoopBackEnLn6",,get_full_name());
      this.AcLoopBackEnLn6.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn6)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn6


class ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn7 extends uvm_reg;
	rand uvm_reg_field AcLoopBackEnLn7;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcLoopBackEnLn7: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn7");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcLoopBackEnLn7 = uvm_reg_field::type_id::create("AcLoopBackEnLn7",,get_full_name());
      this.AcLoopBackEnLn7.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn7)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn7


class ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn8 extends uvm_reg;
	rand uvm_reg_field AcLoopBackEnLn8;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcLoopBackEnLn8: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn8");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcLoopBackEnLn8 = uvm_reg_field::type_id::create("AcLoopBackEnLn8",,get_full_name());
      this.AcLoopBackEnLn8.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn8)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn8


class ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn9 extends uvm_reg;
	rand uvm_reg_field AcLoopBackEnLn9;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcLoopBackEnLn9: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn9");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcLoopBackEnLn9 = uvm_reg_field::type_id::create("AcLoopBackEnLn9",,get_full_name());
      this.AcLoopBackEnLn9.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn9)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn9


class ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn10 extends uvm_reg;
	rand uvm_reg_field AcLoopBackEnLn10;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   AcLoopBackEnLn10: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn10");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.AcLoopBackEnLn10 = uvm_reg_field::type_id::create("AcLoopBackEnLn10",,get_full_name());
      this.AcLoopBackEnLn10.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn10)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn10


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r9_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDly_r9_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly_r9_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDly_r9_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly_r9_p0 = uvm_reg_field::type_id::create("ACXTxDly_r9_p0",,get_full_name());
      this.ACXTxDly_r9_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r9_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r9_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r9_p0 extends uvm_reg;
	rand uvm_reg_field ACXTxDly2nMode_r9_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ACXTxDly2nMode_r9_p0: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r9_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ACXTxDly2nMode_r9_p0 = uvm_reg_field::type_id::create("ACXTxDly2nMode_r9_p0",,get_full_name());
      this.ACXTxDly2nMode_r9_p0.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r9_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r9_p0


class ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE0 extends uvm_reg;
	uvm_reg_field ATestPrbsErrCntSE0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ATestPrbsErrCntSE0: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ATestPrbsErrCntSE0 = uvm_reg_field::type_id::create("ATestPrbsErrCntSE0",,get_full_name());
      this.ATestPrbsErrCntSE0.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE0


class ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE1 extends uvm_reg;
	uvm_reg_field ATestPrbsErrCntSE1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ATestPrbsErrCntSE1: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE1");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ATestPrbsErrCntSE1 = uvm_reg_field::type_id::create("ATestPrbsErrCntSE1",,get_full_name());
      this.ATestPrbsErrCntSE1.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE1


class ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE2 extends uvm_reg;
	uvm_reg_field ATestPrbsErrCntSE2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ATestPrbsErrCntSE2: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ATestPrbsErrCntSE2 = uvm_reg_field::type_id::create("ATestPrbsErrCntSE2",,get_full_name());
      this.ATestPrbsErrCntSE2.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE2


class ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE3 extends uvm_reg;
	uvm_reg_field ATestPrbsErrCntSE3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ATestPrbsErrCntSE3: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ATestPrbsErrCntSE3 = uvm_reg_field::type_id::create("ATestPrbsErrCntSE3",,get_full_name());
      this.ATestPrbsErrCntSE3.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE3


class ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE4 extends uvm_reg;
	uvm_reg_field ATestPrbsErrCntSE4;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ATestPrbsErrCntSE4: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE4");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ATestPrbsErrCntSE4 = uvm_reg_field::type_id::create("ATestPrbsErrCntSE4",,get_full_name());
      this.ATestPrbsErrCntSE4.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE4)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE4


class ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE5 extends uvm_reg;
	uvm_reg_field ATestPrbsErrCntSE5;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ATestPrbsErrCntSE5: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE5");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ATestPrbsErrCntSE5 = uvm_reg_field::type_id::create("ATestPrbsErrCntSE5",,get_full_name());
      this.ATestPrbsErrCntSE5.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE5)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE5


class ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE6 extends uvm_reg;
	uvm_reg_field ATestPrbsErrCntSE6;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ATestPrbsErrCntSE6: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE6");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ATestPrbsErrCntSE6 = uvm_reg_field::type_id::create("ATestPrbsErrCntSE6",,get_full_name());
      this.ATestPrbsErrCntSE6.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE6)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE6


class ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE7 extends uvm_reg;
	uvm_reg_field ATestPrbsErrCntSE7;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ATestPrbsErrCntSE7: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE7");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ATestPrbsErrCntSE7 = uvm_reg_field::type_id::create("ATestPrbsErrCntSE7",,get_full_name());
      this.ATestPrbsErrCntSE7.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE7)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE7


class ral_block_DWC_DDRPHYA_AC1_p0 extends uvm_reg_block;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcPipeEn_p0 AcPipeEn_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_CKDllStopCal CKDllStopCal;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_CkVal_p0 CkVal_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_CkDisVal_p0 CkDisVal_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_DTOBypassEn DTOBypassEn;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACSingleEndedMode_p0 ACSingleEndedMode_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_InitSeqControl InitSeqControl;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_MtestMuxSel MtestMuxSel;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_PorControl PorControl;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ClrPORMemReset ClrPORMemReset;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_MemResetL MemResetL;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_CMOSxHardMacroModeSel CMOSxHardMacroModeSel;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_RxAcVrefControl_p0 RxAcVrefControl_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_MemResetLStatus MemResetLStatus;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACDlyScaleGatingDisable ACDlyScaleGatingDisable;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_LcdlCalControl LcdlCalControl;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACParityInvert ACParityInvert;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACPulseDllUpdatePhase ACPulseDllUpdatePhase;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ScratchPadAC ScratchPadAC;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ATestMode ATestMode;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcDigStrobeGenSel AcDigStrobeGenSel;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcDigStrobePat AcDigStrobePat;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcOdtEn AcOdtEn;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcRxStrobeEnPat AcRxStrobeEnPat;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ATxDlySelect_p0 ATxDlySelect_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_MapCA0toDfi MapCA0toDfi;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_MapCA1toDfi MapCA1toDfi;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_MapCA2toDfi MapCA2toDfi;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_MapCA3toDfi MapCA3toDfi;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_MapCA4toDfi MapCA4toDfi;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_MapCA5toDfi MapCA5toDfi;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_MapCA6toDfi MapCA6toDfi;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcTxMode AsyncAcTxMode;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcRxMode AsyncAcRxMode;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcTxEn AsyncAcTxEn;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcTxData AsyncAcTxData;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcRxData AsyncAcRxData;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ForceClkDisable ForceClkDisable;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_CaBusTriEn CaBusTriEn;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcLnDisable AcLnDisable;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_DfiClkAcLnDis DfiClkAcLnDis;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_PClkAcLnDis PClkAcLnDis;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcLcdlCalPhDetOut AcLcdlCalPhDetOut;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r0_p0 ACXTxDly_r0_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_CKXTxDly_p0 CKXTxDly_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDlyDTO_p0 ACXTxDlyDTO_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r0_p0 ACXTxDly2nMode_r0_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcLcdlUpdInterval_p0 AcLcdlUpdInterval_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_LcdlCalSeqUpdCK_p0 LcdlCalSeqUpdCK_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_CkTriEn CkTriEn;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACReserved0 ACReserved0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_LcdlCalCtrl LcdlCalCtrl;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_PUBReservedP1_p0 PUBReservedP1_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCDCtrl_p0 PclkDCDCtrl_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ForceInternalUpdate ForceInternalUpdate;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSEC0 ATestPrbsErrCntSEC0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSEC1 ATestPrbsErrCntSEC1;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcPDsampleSEC0 AcPDsampleSEC0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcPDsampleSEC1 AcPDsampleSEC1;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcPDsampleDIFF AcPDsampleDIFF;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r1_p0 ACXTxDly_r1_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r1_p0 ACXTxDly2nMode_r1_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r2_p0 ACXTxDly_r2_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r2_p0 ACXTxDly2nMode_r2_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r3_p0 ACXTxDly_r3_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r3_p0 ACXTxDly2nMode_r3_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntDIFF0T ATestPrbsErrCntDIFF0T;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntDIFF0C ATestPrbsErrCntDIFF0C;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r4_p0 ACXTxDly_r4_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r4_p0 ACXTxDly2nMode_r4_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r5_p0 ACXTxDly_r5_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r5_p0 ACXTxDly2nMode_r5_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r6_p0 ACXTxDly_r6_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r6_p0 ACXTxDly2nMode_r6_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r7_p0 ACXTxDly_r7_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r7_p0 ACXTxDly2nMode_r7_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCACalCtrl0AC PclkDCACalCtrl0AC;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCADynCtrl PclkDCADynCtrl;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCAStaticCtrl0AC_p0 PclkDCAStaticCtrl0AC_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCASampCntAC PclkDCASampCntAC;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCAHysMaskAC PclkDCAHysMaskAC;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCACalFineBoundAC PclkDCACalFineBoundAC;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCANextFineOnCoarseAC PclkDCANextFineOnCoarseAC;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCAFullSearchIVACAC PclkDCAFullSearchIVACAC;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_LcdlTstCtrl LcdlTstCtrl;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r8_p0 ACXTxDly_r8_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r8_p0 ACXTxDly2nMode_r8_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn0 AcLoopBackEnLn0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn1 AcLoopBackEnLn1;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn2 AcLoopBackEnLn2;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn3 AcLoopBackEnLn3;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn4 AcLoopBackEnLn4;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn5 AcLoopBackEnLn5;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn6 AcLoopBackEnLn6;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn7 AcLoopBackEnLn7;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn8 AcLoopBackEnLn8;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn9 AcLoopBackEnLn9;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn10 AcLoopBackEnLn10;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r9_p0 ACXTxDly_r9_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r9_p0 ACXTxDly2nMode_r9_p0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE0 ATestPrbsErrCntSE0;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE1 ATestPrbsErrCntSE1;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE2 ATestPrbsErrCntSE2;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE3 ATestPrbsErrCntSE3;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE4 ATestPrbsErrCntSE4;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE5 ATestPrbsErrCntSE5;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE6 ATestPrbsErrCntSE6;
	rand ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE7 ATestPrbsErrCntSE7;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field AcPipeEn_p0_AcPipeEn_p0;
	rand uvm_reg_field CKDllStopCal_CKDllStopCal;
	rand uvm_reg_field CkVal_p0_CkVal_p0;
	uvm_reg_field CkDisVal_p0_Reserved;
	uvm_reg_field Reserved;
	rand uvm_reg_field CkDisVal_p0_CkDisVal_p0;
	rand uvm_reg_field DTOBypassEn_DTOBypassEn;
	rand uvm_reg_field ACSingleEndedMode_p0_SingleEndedCK;
	rand uvm_reg_field SingleEndedCK;
	rand uvm_reg_field InitSeqControl_InhibitTxRdPtrBypassForce;
	rand uvm_reg_field InhibitTxRdPtrBypassForce;
	rand uvm_reg_field InitSeqControl_InhibitTxRdPtrRstLclCal;
	rand uvm_reg_field InhibitTxRdPtrRstLclCal;
	rand uvm_reg_field InitSeqControl_InitControlRstLclCal;
	rand uvm_reg_field InitControlRstLclCal;
	rand uvm_reg_field InitSeqControl_InhibitTxRdPtrRxReplLcdlInit;
	rand uvm_reg_field InhibitTxRdPtrRxReplLcdlInit;
	rand uvm_reg_field InitSeqControl_InitControlRxReplLcdlInit;
	rand uvm_reg_field InitControlRxReplLcdlInit;
	rand uvm_reg_field InitSeqControl_InhibitTxRdPtrTXFIFOInit;
	rand uvm_reg_field InhibitTxRdPtrTXFIFOInit;
	rand uvm_reg_field InitSeqControl_InitControlTXFIFOInit;
	rand uvm_reg_field InitControlTXFIFOInit;
	rand uvm_reg_field InitSeqControl_InhibitTxRdPtrDbDataPipeInit;
	rand uvm_reg_field InhibitTxRdPtrDbDataPipeInit;
	rand uvm_reg_field InitSeqControl_InhibitTxRdPtrDbRxEnPhUpdInit;
	rand uvm_reg_field InhibitTxRdPtrDbRxEnPhUpdInit;
	rand uvm_reg_field InitSeqControl_InitControlDbDataPipeInit;
	rand uvm_reg_field InitControlDbDataPipeInit;
	rand uvm_reg_field InitSeqControl_InhibitTxRdPtrDbPptInit;
	rand uvm_reg_field InhibitTxRdPtrDbPptInit;
	rand uvm_reg_field InitSeqControl_InitControlDbPptInit;
	rand uvm_reg_field InitControlDbPptInit;
	rand uvm_reg_field InitSeqControl_InitControlDbRxEnPhUpdInit;
	rand uvm_reg_field InitControlDbRxEnPhUpdInit;
	rand uvm_reg_field InitSeqControl_InhibitTxRdPtrRxReplSeqInit;
	rand uvm_reg_field InhibitTxRdPtrRxReplSeqInit;
	rand uvm_reg_field InitSeqControl_InitControlRxReplSeqInit;
	rand uvm_reg_field InitControlRxReplSeqInit;
	rand uvm_reg_field InitSeqControl_ReservedInitSeqControl;
	rand uvm_reg_field ReservedInitSeqControl;
	rand uvm_reg_field MtestMuxSel_MtestMuxSel;
	rand uvm_reg_field PorControl_PwrOkDlyCtrl;
	rand uvm_reg_field PwrOkDlyCtrl;
	rand uvm_reg_field ClrPORMemReset_ClrPORMemReset;
	rand uvm_reg_field MemResetL_MemResetLValue;
	rand uvm_reg_field MemResetLValue;
	rand uvm_reg_field MemResetL_ProtectMemReset;
	rand uvm_reg_field ProtectMemReset;
	rand uvm_reg_field MemResetL_AsyncMemResetLRxMode;
	rand uvm_reg_field AsyncMemResetLRxMode;
	rand uvm_reg_field CMOSxHardMacroModeSel_CMOSxHardMacroModeSel;
	rand uvm_reg_field RxAcVrefControl_p0_RxAcVrefDac;
	rand uvm_reg_field RxAcVrefDac;
	rand uvm_reg_field RxAcVrefControl_p0_RxAcVrefDacEn;
	rand uvm_reg_field RxAcVrefDacEn;
	uvm_reg_field MemResetLStatus_PORMemReset;
	uvm_reg_field PORMemReset;
	uvm_reg_field MemResetLStatus_AsyncMemResetLRxData;
	uvm_reg_field AsyncMemResetLRxData;
	rand uvm_reg_field ACDlyScaleGatingDisable_ACDlyScaleGatingDisable;
	rand uvm_reg_field LcdlCalControl_LcdlCalResetRelock;
	rand uvm_reg_field LcdlCalResetRelock;
	rand uvm_reg_field LcdlCalControl_LcdlCalStop;
	rand uvm_reg_field LcdlCalStop;
	rand uvm_reg_field LcdlCalControl_LcdlUpdTrackDis;
	rand uvm_reg_field LcdlUpdTrackDis;
	rand uvm_reg_field ACParityInvert_ACParityInvert;
	rand uvm_reg_field ACPulseDllUpdatePhase_ACPulseDllUpdatePhase;
	rand uvm_reg_field ScratchPadAC_ScratchPadAC;
	rand uvm_reg_field ATestMode_ATestPrbsEn;
	rand uvm_reg_field ATestPrbsEn;
	rand uvm_reg_field ATestMode_ATestPrbs7or15Mode;
	rand uvm_reg_field ATestPrbs7or15Mode;
	rand uvm_reg_field ATestMode_ReservedATestMode42;
	rand uvm_reg_field ReservedATestMode42;
	rand uvm_reg_field ATestMode_ATestPrbsChkmode;
	rand uvm_reg_field ATestPrbsChkmode;
	rand uvm_reg_field ATestMode_PrbsDdrMode;
	rand uvm_reg_field PrbsDdrMode;
	rand uvm_reg_field ATestMode_ReservedATestMode7;
	rand uvm_reg_field ReservedATestMode7;
	rand uvm_reg_field AcDigStrobeGenSel_AcDigStrobeGenSel;
	rand uvm_reg_field AcDigStrobePat_AcDigStrobePat;
	rand uvm_reg_field AcOdtEn_AcOdtEn;
	rand uvm_reg_field AcRxStrobeEnPat_AcRxStrobeEnPat;
	rand uvm_reg_field ATxDlySelect_p0_ATxDlySelect_p0;
	rand uvm_reg_field MapCA0toDfi_MapCA0toDfi;
	rand uvm_reg_field MapCA1toDfi_MapCA1toDfi;
	rand uvm_reg_field MapCA2toDfi_MapCA2toDfi;
	rand uvm_reg_field MapCA3toDfi_MapCA3toDfi;
	rand uvm_reg_field MapCA4toDfi_MapCA4toDfi;
	rand uvm_reg_field MapCA5toDfi_MapCA5toDfi;
	rand uvm_reg_field MapCA6toDfi_MapCA6toDfi;
	rand uvm_reg_field AsyncAcTxMode_AsyncAcTxMode;
	rand uvm_reg_field AsyncAcRxMode_AsyncAcRxMode;
	rand uvm_reg_field AsyncAcTxEn_AsyncAcTxEn;
	rand uvm_reg_field AsyncAcTxData_AsyncAcTxData;
	uvm_reg_field AsyncAcRxData_AsyncAcRxData;
	rand uvm_reg_field ForceClkDisable_ForceClkDisable;
	rand uvm_reg_field CaBusTriEn_CaBusTriEn;
	rand uvm_reg_field AcLnDisable_AcLnDisable;
	rand uvm_reg_field DfiClkAcLnDis_DfiClkAcLnDis;
	rand uvm_reg_field PClkAcLnDis_PClkAcLnDis;
	uvm_reg_field AcLcdlCalPhDetOut_AcLcdlCalPhDetOut;
	rand uvm_reg_field ACXTxDly_r0_p0_ACXTxDly_r0_p0;
	rand uvm_reg_field CKXTxDly_p0_CKXTxDly_p0;
	rand uvm_reg_field ACXTxDlyDTO_p0_ACXTxDlyDTO_p0;
	rand uvm_reg_field ACXTxDly2nMode_r0_p0_ACXTxDly2nMode_r0_p0;
	rand uvm_reg_field AcLcdlUpdInterval_p0_AcLcdlUpdInterval_p0;
	rand uvm_reg_field LcdlCalSeqUpdCK_p0_LcdlCalSeqUpdCK_p0;
	rand uvm_reg_field CkTriEn_CkTriEn;
	rand uvm_reg_field ACReserved0_ACReserved0;
	rand uvm_reg_field LcdlCalCtrl_LcdlCalCtrl;
	rand uvm_reg_field PUBReservedP1_p0_PUBReservedP1_p0;
	rand uvm_reg_field PclkDCDCtrl_p0_PclkDCDEn;
	rand uvm_reg_field PclkDCDEn;
	rand uvm_reg_field PclkDCDCtrl_p0_PclkDCDOffsetMode;
	rand uvm_reg_field PclkDCDOffsetMode;
	rand uvm_reg_field ForceInternalUpdate_ForceInternalUpdate;
	uvm_reg_field ATestPrbsErrCntSEC0_ATestPrbsErrCntSEC0;
	uvm_reg_field ATestPrbsErrCntSEC1_ATestPrbsErrCntSEC1;
	uvm_reg_field AcPDsampleSEC0_AcPDsampleSEC0;
	uvm_reg_field AcPDsampleSEC1_AcPDsampleSEC1;
	uvm_reg_field AcPDsampleDIFF_PDsampleT;
	uvm_reg_field PDsampleT;
	uvm_reg_field AcPDsampleDIFF_PDsampleC;
	uvm_reg_field PDsampleC;
	rand uvm_reg_field ACXTxDly_r1_p0_ACXTxDly_r1_p0;
	rand uvm_reg_field ACXTxDly2nMode_r1_p0_ACXTxDly2nMode_r1_p0;
	rand uvm_reg_field ACXTxDly_r2_p0_ACXTxDly_r2_p0;
	rand uvm_reg_field ACXTxDly2nMode_r2_p0_ACXTxDly2nMode_r2_p0;
	rand uvm_reg_field ACXTxDly_r3_p0_ACXTxDly_r3_p0;
	rand uvm_reg_field ACXTxDly2nMode_r3_p0_ACXTxDly2nMode_r3_p0;
	uvm_reg_field ATestPrbsErrCntDIFF0T_ATestPrbsErrCntDIFF0T;
	uvm_reg_field ATestPrbsErrCntDIFF0C_ATestPrbsErrCntDIFF0C;
	rand uvm_reg_field ACXTxDly_r4_p0_ACXTxDly_r4_p0;
	rand uvm_reg_field ACXTxDly2nMode_r4_p0_ACXTxDly2nMode_r4_p0;
	rand uvm_reg_field ACXTxDly_r5_p0_ACXTxDly_r5_p0;
	rand uvm_reg_field ACXTxDly2nMode_r5_p0_ACXTxDly2nMode_r5_p0;
	rand uvm_reg_field ACXTxDly_r6_p0_ACXTxDly_r6_p0;
	rand uvm_reg_field ACXTxDly2nMode_r6_p0_ACXTxDly2nMode_r6_p0;
	rand uvm_reg_field ACXTxDly_r7_p0_ACXTxDly_r7_p0;
	rand uvm_reg_field ACXTxDly2nMode_r7_p0_ACXTxDly2nMode_r7_p0;
	rand uvm_reg_field PclkDCACalCtrl0AC_PclkDCAIncOnHiAC;
	rand uvm_reg_field PclkDCAIncOnHiAC;
	rand uvm_reg_field PclkDCACalCtrl0AC_PclkDCAIncOnLoAC;
	rand uvm_reg_field PclkDCAIncOnLoAC;
	rand uvm_reg_field PclkDCACalCtrl0AC_PclkDCADecOnHiAC;
	rand uvm_reg_field PclkDCADecOnHiAC;
	rand uvm_reg_field PclkDCACalCtrl0AC_PclkDCADecOnLoAC;
	rand uvm_reg_field PclkDCADecOnLoAC;
	rand uvm_reg_field PclkDCADynCtrl_PclkDCACalReset;
	rand uvm_reg_field PclkDCACalReset;
	rand uvm_reg_field PclkDCADynCtrl_PclkDCAQuickSearch;
	rand uvm_reg_field PclkDCAQuickSearch;
	rand uvm_reg_field PclkDCADynCtrl_PclkDCAForceSampVld;
	rand uvm_reg_field PclkDCAForceSampVld;
	rand uvm_reg_field PclkDCADynCtrl_PclkDCAForceUpd;
	rand uvm_reg_field PclkDCAForceUpd;
	rand uvm_reg_field PclkDCAStaticCtrl0AC_p0_PclkDCACalModeAC;
	rand uvm_reg_field PclkDCACalModeAC;
	rand uvm_reg_field PclkDCAStaticCtrl0AC_p0_PclkDCAEnAC;
	rand uvm_reg_field PclkDCAEnAC;
	rand uvm_reg_field PclkDCAStaticCtrl0AC_p0_PclkDCATxLcdlPhSelAC;
	rand uvm_reg_field PclkDCATxLcdlPhSelAC;
	rand uvm_reg_field PclkDCAStaticCtrl0AC_p0_PclkDCDSettleAC;
	rand uvm_reg_field PclkDCDSettleAC;
	rand uvm_reg_field PclkDCAStaticCtrl0AC_p0_PclkDCDSampTimeAC;
	rand uvm_reg_field PclkDCDSampTimeAC;
	rand uvm_reg_field PclkDCASampCntAC_PclkDCAQkSampCntAC;
	rand uvm_reg_field PclkDCAQkSampCntAC;
	rand uvm_reg_field PclkDCASampCntAC_PclkDCAFineSampCntAAC;
	rand uvm_reg_field PclkDCAFineSampCntAAC;
	rand uvm_reg_field PclkDCASampCntAC_PclkDCAFineSampCntBAC;
	rand uvm_reg_field PclkDCAFineSampCntBAC;
	rand uvm_reg_field PclkDCASampCntAC_PclkDCACoarseSampCntAC;
	rand uvm_reg_field PclkDCACoarseSampCntAC;
	rand uvm_reg_field PclkDCAHysMaskAC_PclkDCAHysMaskAC;
	rand uvm_reg_field PclkDCACalFineBoundAC_PclkDCAURMaxFineAC;
	rand uvm_reg_field PclkDCAURMaxFineAC;
	rand uvm_reg_field PclkDCACalFineBoundAC_PclkDCAURMinFineAC;
	rand uvm_reg_field PclkDCAURMinFineAC;
	rand uvm_reg_field PclkDCACalFineBoundAC_PclkDCALLMaxFineAC;
	rand uvm_reg_field PclkDCALLMaxFineAC;
	rand uvm_reg_field PclkDCACalFineBoundAC_PclkDCALLMinFineAC;
	rand uvm_reg_field PclkDCALLMinFineAC;
	rand uvm_reg_field PclkDCANextFineOnCoarseAC_PclkDCACoarseIncFineURAC;
	rand uvm_reg_field PclkDCACoarseIncFineURAC;
	rand uvm_reg_field PclkDCANextFineOnCoarseAC_PclkDCACoarseDecFineURAC;
	rand uvm_reg_field PclkDCACoarseDecFineURAC;
	rand uvm_reg_field PclkDCANextFineOnCoarseAC_PclkDCACoarseIncFineLLAC;
	rand uvm_reg_field PclkDCACoarseIncFineLLAC;
	rand uvm_reg_field PclkDCANextFineOnCoarseAC_PclkDCACoarseDecFineLLAC;
	rand uvm_reg_field PclkDCACoarseDecFineLLAC;
	rand uvm_reg_field PclkDCAFullSearchIVACAC_PclkDCAFineIVMaxAC;
	rand uvm_reg_field PclkDCAFineIVMaxAC;
	rand uvm_reg_field PclkDCAFullSearchIVACAC_PclkDCAFineIVMinAC;
	rand uvm_reg_field PclkDCAFineIVMinAC;
	rand uvm_reg_field LcdlTstCtrl_LcdlTstCtrl;
	rand uvm_reg_field ACXTxDly_r8_p0_ACXTxDly_r8_p0;
	rand uvm_reg_field ACXTxDly2nMode_r8_p0_ACXTxDly2nMode_r8_p0;
	rand uvm_reg_field AcLoopBackEnLn0_AcLoopBackEnLn0;
	rand uvm_reg_field AcLoopBackEnLn1_AcLoopBackEnLn1;
	rand uvm_reg_field AcLoopBackEnLn2_AcLoopBackEnLn2;
	rand uvm_reg_field AcLoopBackEnLn3_AcLoopBackEnLn3;
	rand uvm_reg_field AcLoopBackEnLn4_AcLoopBackEnLn4;
	rand uvm_reg_field AcLoopBackEnLn5_AcLoopBackEnLn5;
	rand uvm_reg_field AcLoopBackEnLn6_AcLoopBackEnLn6;
	rand uvm_reg_field AcLoopBackEnLn7_AcLoopBackEnLn7;
	rand uvm_reg_field AcLoopBackEnLn8_AcLoopBackEnLn8;
	rand uvm_reg_field AcLoopBackEnLn9_AcLoopBackEnLn9;
	rand uvm_reg_field AcLoopBackEnLn10_AcLoopBackEnLn10;
	rand uvm_reg_field ACXTxDly_r9_p0_ACXTxDly_r9_p0;
	rand uvm_reg_field ACXTxDly2nMode_r9_p0_ACXTxDly2nMode_r9_p0;
	uvm_reg_field ATestPrbsErrCntSE0_ATestPrbsErrCntSE0;
	uvm_reg_field ATestPrbsErrCntSE1_ATestPrbsErrCntSE1;
	uvm_reg_field ATestPrbsErrCntSE2_ATestPrbsErrCntSE2;
	uvm_reg_field ATestPrbsErrCntSE3_ATestPrbsErrCntSE3;
	uvm_reg_field ATestPrbsErrCntSE4_ATestPrbsErrCntSE4;
	uvm_reg_field ATestPrbsErrCntSE5_ATestPrbsErrCntSE5;
	uvm_reg_field ATestPrbsErrCntSE6_ATestPrbsErrCntSE6;
	uvm_reg_field ATestPrbsErrCntSE7_ATestPrbsErrCntSE7;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	AcPipeEn_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h8 };
		option.weight = 1;
	}

	CKDllStopCal : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA };
		option.weight = 1;
	}

	CkVal_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hE };
		option.weight = 1;
	}

	CkDisVal_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF };
		option.weight = 1;
	}

	DTOBypassEn : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h10 };
		option.weight = 1;
	}

	ACSingleEndedMode_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h15 };
		option.weight = 1;
	}

	InitSeqControl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h16 };
		option.weight = 1;
	}

	MtestMuxSel : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1A };
		option.weight = 1;
	}

	PorControl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h20 };
		option.weight = 1;
	}

	ClrPORMemReset : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h21 };
		option.weight = 1;
	}

	MemResetL : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h22 };
		option.weight = 1;
	}

	CMOSxHardMacroModeSel : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h24 };
		option.weight = 1;
	}

	RxAcVrefControl_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h25 };
		option.weight = 1;
	}

	MemResetLStatus : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h26 };
		option.weight = 1;
	}

	ACDlyScaleGatingDisable : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h27 };
		option.weight = 1;
	}

	LcdlCalControl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h47 };
		option.weight = 1;
	}

	ACParityInvert : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4D };
		option.weight = 1;
	}

	ACPulseDllUpdatePhase : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h79 };
		option.weight = 1;
	}

	ScratchPadAC : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h7D };
		option.weight = 1;
	}

	ATestMode : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h7F };
		option.weight = 1;
	}

	AcDigStrobeGenSel : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h86 };
		option.weight = 1;
	}

	AcDigStrobePat : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h87 };
		option.weight = 1;
	}

	AcOdtEn : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h88 };
		option.weight = 1;
	}

	AcRxStrobeEnPat : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h89 };
		option.weight = 1;
	}

	ATxDlySelect_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h8F };
		option.weight = 1;
	}

	MapCA0toDfi : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h90 };
		option.weight = 1;
	}

	MapCA1toDfi : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h91 };
		option.weight = 1;
	}

	MapCA2toDfi : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h92 };
		option.weight = 1;
	}

	MapCA3toDfi : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h93 };
		option.weight = 1;
	}

	MapCA4toDfi : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h94 };
		option.weight = 1;
	}

	MapCA5toDfi : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h95 };
		option.weight = 1;
	}

	MapCA6toDfi : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h96 };
		option.weight = 1;
	}

	AsyncAcTxMode : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA0 };
		option.weight = 1;
	}

	AsyncAcRxMode : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA1 };
		option.weight = 1;
	}

	AsyncAcTxEn : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA2 };
		option.weight = 1;
	}

	AsyncAcTxData : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA3 };
		option.weight = 1;
	}

	AsyncAcRxData : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA5 };
		option.weight = 1;
	}

	ForceClkDisable : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA6 };
		option.weight = 1;
	}

	CaBusTriEn : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hAB };
		option.weight = 1;
	}

	AcLnDisable : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hAC };
		option.weight = 1;
	}

	DfiClkAcLnDis : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hAD };
		option.weight = 1;
	}

	PClkAcLnDis : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hAE };
		option.weight = 1;
	}

	AcLcdlCalPhDetOut : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hAF };
		option.weight = 1;
	}

	ACXTxDly_r0_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD8 };
		option.weight = 1;
	}

	CKXTxDly_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD9 };
		option.weight = 1;
	}

	ACXTxDlyDTO_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hDA };
		option.weight = 1;
	}

	ACXTxDly2nMode_r0_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hDE };
		option.weight = 1;
	}

	AcLcdlUpdInterval_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hEB };
		option.weight = 1;
	}

	LcdlCalSeqUpdCK_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hEC };
		option.weight = 1;
	}

	CkTriEn : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hED };
		option.weight = 1;
	}

	ACReserved0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF9 };
		option.weight = 1;
	}

	LcdlCalCtrl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFE };
		option.weight = 1;
	}

	PUBReservedP1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFF };
		option.weight = 1;
	}

	PclkDCDCtrl_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h100 };
		option.weight = 1;
	}

	ForceInternalUpdate : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h103 };
		option.weight = 1;
	}

	ATestPrbsErrCntSEC0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1A8 };
		option.weight = 1;
	}

	ATestPrbsErrCntSEC1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1A9 };
		option.weight = 1;
	}

	AcPDsampleSEC0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1B8 };
		option.weight = 1;
	}

	AcPDsampleSEC1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1B9 };
		option.weight = 1;
	}

	AcPDsampleDIFF : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1CA };
		option.weight = 1;
	}

	ACXTxDly_r1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1D8 };
		option.weight = 1;
	}

	ACXTxDly2nMode_r1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1DE };
		option.weight = 1;
	}

	ACXTxDly_r2_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2D8 };
		option.weight = 1;
	}

	ACXTxDly2nMode_r2_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2DE };
		option.weight = 1;
	}

	ACXTxDly_r3_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3D8 };
		option.weight = 1;
	}

	ACXTxDly2nMode_r3_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3DE };
		option.weight = 1;
	}

	ATestPrbsErrCntDIFF0T : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3E0 };
		option.weight = 1;
	}

	ATestPrbsErrCntDIFF0C : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3E4 };
		option.weight = 1;
	}

	ACXTxDly_r4_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4D8 };
		option.weight = 1;
	}

	ACXTxDly2nMode_r4_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4DE };
		option.weight = 1;
	}

	ACXTxDly_r5_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5D8 };
		option.weight = 1;
	}

	ACXTxDly2nMode_r5_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5DE };
		option.weight = 1;
	}

	ACXTxDly_r6_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h6D8 };
		option.weight = 1;
	}

	ACXTxDly2nMode_r6_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h6DE };
		option.weight = 1;
	}

	ACXTxDly_r7_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h7D8 };
		option.weight = 1;
	}

	ACXTxDly2nMode_r7_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h7DE };
		option.weight = 1;
	}

	PclkDCACalCtrl0AC : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h800 };
		option.weight = 1;
	}

	PclkDCADynCtrl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h802 };
		option.weight = 1;
	}

	PclkDCAStaticCtrl0AC_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h803 };
		option.weight = 1;
	}

	PclkDCASampCntAC : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h804 };
		option.weight = 1;
	}

	PclkDCAHysMaskAC : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h805 };
		option.weight = 1;
	}

	PclkDCACalFineBoundAC : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h806 };
		option.weight = 1;
	}

	PclkDCANextFineOnCoarseAC : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h807 };
		option.weight = 1;
	}

	PclkDCAFullSearchIVACAC : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h808 };
		option.weight = 1;
	}

	LcdlTstCtrl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h884 };
		option.weight = 1;
	}

	ACXTxDly_r8_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h8D8 };
		option.weight = 1;
	}

	ACXTxDly2nMode_r8_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h8DE };
		option.weight = 1;
	}

	AcLoopBackEnLn0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h900 };
		option.weight = 1;
	}

	AcLoopBackEnLn1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h901 };
		option.weight = 1;
	}

	AcLoopBackEnLn2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h902 };
		option.weight = 1;
	}

	AcLoopBackEnLn3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h903 };
		option.weight = 1;
	}

	AcLoopBackEnLn4 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h904 };
		option.weight = 1;
	}

	AcLoopBackEnLn5 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h905 };
		option.weight = 1;
	}

	AcLoopBackEnLn6 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h906 };
		option.weight = 1;
	}

	AcLoopBackEnLn7 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h907 };
		option.weight = 1;
	}

	AcLoopBackEnLn8 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h908 };
		option.weight = 1;
	}

	AcLoopBackEnLn9 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h909 };
		option.weight = 1;
	}

	AcLoopBackEnLn10 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h90A };
		option.weight = 1;
	}

	ACXTxDly_r9_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h9D8 };
		option.weight = 1;
	}

	ACXTxDly2nMode_r9_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h9DE };
		option.weight = 1;
	}

	ATestPrbsErrCntSE0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB00 };
		option.weight = 1;
	}

	ATestPrbsErrCntSE1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB01 };
		option.weight = 1;
	}

	ATestPrbsErrCntSE2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB02 };
		option.weight = 1;
	}

	ATestPrbsErrCntSE3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB03 };
		option.weight = 1;
	}

	ATestPrbsErrCntSE4 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB04 };
		option.weight = 1;
	}

	ATestPrbsErrCntSE5 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB05 };
		option.weight = 1;
	}

	ATestPrbsErrCntSE6 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB06 };
		option.weight = 1;
	}

	ATestPrbsErrCntSE7 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB07 };
		option.weight = 1;
	}
endgroup
	function new(string name = "DWC_DDRPHYA_AC1_p0");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.AcPipeEn_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_AcPipeEn_p0::type_id::create("AcPipeEn_p0",,get_full_name());
      if(this.AcPipeEn_p0.has_coverage(UVM_CVR_ALL))
      	this.AcPipeEn_p0.cg_bits.option.name = {get_name(), ".", "AcPipeEn_p0_bits"};
      this.AcPipeEn_p0.configure(this, null, "");
      this.AcPipeEn_p0.build();
      this.default_map.add_reg(this.AcPipeEn_p0, `UVM_REG_ADDR_WIDTH'h8, "RW", 0);
		this.AcPipeEn_p0_AcPipeEn_p0 = this.AcPipeEn_p0.AcPipeEn_p0;
      this.CKDllStopCal = ral_reg_DWC_DDRPHYA_AC1_p0_CKDllStopCal::type_id::create("CKDllStopCal",,get_full_name());
      if(this.CKDllStopCal.has_coverage(UVM_CVR_ALL))
      	this.CKDllStopCal.cg_bits.option.name = {get_name(), ".", "CKDllStopCal_bits"};
      this.CKDllStopCal.configure(this, null, "");
      this.CKDllStopCal.build();
      this.default_map.add_reg(this.CKDllStopCal, `UVM_REG_ADDR_WIDTH'hA, "RW", 0);
		this.CKDllStopCal_CKDllStopCal = this.CKDllStopCal.CKDllStopCal;
      this.CkVal_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_CkVal_p0::type_id::create("CkVal_p0",,get_full_name());
      if(this.CkVal_p0.has_coverage(UVM_CVR_ALL))
      	this.CkVal_p0.cg_bits.option.name = {get_name(), ".", "CkVal_p0_bits"};
      this.CkVal_p0.configure(this, null, "");
      this.CkVal_p0.build();
      this.default_map.add_reg(this.CkVal_p0, `UVM_REG_ADDR_WIDTH'hE, "RW", 0);
		this.CkVal_p0_CkVal_p0 = this.CkVal_p0.CkVal_p0;
      this.CkDisVal_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_CkDisVal_p0::type_id::create("CkDisVal_p0",,get_full_name());
      if(this.CkDisVal_p0.has_coverage(UVM_CVR_ALL))
      	this.CkDisVal_p0.cg_bits.option.name = {get_name(), ".", "CkDisVal_p0_bits"};
      this.CkDisVal_p0.configure(this, null, "");
      this.CkDisVal_p0.build();
      this.default_map.add_reg(this.CkDisVal_p0, `UVM_REG_ADDR_WIDTH'hF, "RW", 0);
		this.CkDisVal_p0_Reserved = this.CkDisVal_p0.Reserved;
		this.Reserved = this.CkDisVal_p0.Reserved;
		this.CkDisVal_p0_CkDisVal_p0 = this.CkDisVal_p0.CkDisVal_p0;
      this.DTOBypassEn = ral_reg_DWC_DDRPHYA_AC1_p0_DTOBypassEn::type_id::create("DTOBypassEn",,get_full_name());
      if(this.DTOBypassEn.has_coverage(UVM_CVR_ALL))
      	this.DTOBypassEn.cg_bits.option.name = {get_name(), ".", "DTOBypassEn_bits"};
      this.DTOBypassEn.configure(this, null, "");
      this.DTOBypassEn.build();
      this.default_map.add_reg(this.DTOBypassEn, `UVM_REG_ADDR_WIDTH'h10, "RW", 0);
		this.DTOBypassEn_DTOBypassEn = this.DTOBypassEn.DTOBypassEn;
      this.ACSingleEndedMode_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACSingleEndedMode_p0::type_id::create("ACSingleEndedMode_p0",,get_full_name());
      if(this.ACSingleEndedMode_p0.has_coverage(UVM_CVR_ALL))
      	this.ACSingleEndedMode_p0.cg_bits.option.name = {get_name(), ".", "ACSingleEndedMode_p0_bits"};
      this.ACSingleEndedMode_p0.configure(this, null, "");
      this.ACSingleEndedMode_p0.build();
      this.default_map.add_reg(this.ACSingleEndedMode_p0, `UVM_REG_ADDR_WIDTH'h15, "RW", 0);
		this.ACSingleEndedMode_p0_SingleEndedCK = this.ACSingleEndedMode_p0.SingleEndedCK;
		this.SingleEndedCK = this.ACSingleEndedMode_p0.SingleEndedCK;
      this.InitSeqControl = ral_reg_DWC_DDRPHYA_AC1_p0_InitSeqControl::type_id::create("InitSeqControl",,get_full_name());
      if(this.InitSeqControl.has_coverage(UVM_CVR_ALL))
      	this.InitSeqControl.cg_bits.option.name = {get_name(), ".", "InitSeqControl_bits"};
      this.InitSeqControl.configure(this, null, "");
      this.InitSeqControl.build();
      this.default_map.add_reg(this.InitSeqControl, `UVM_REG_ADDR_WIDTH'h16, "RW", 0);
		this.InitSeqControl_InhibitTxRdPtrBypassForce = this.InitSeqControl.InhibitTxRdPtrBypassForce;
		this.InhibitTxRdPtrBypassForce = this.InitSeqControl.InhibitTxRdPtrBypassForce;
		this.InitSeqControl_InhibitTxRdPtrRstLclCal = this.InitSeqControl.InhibitTxRdPtrRstLclCal;
		this.InhibitTxRdPtrRstLclCal = this.InitSeqControl.InhibitTxRdPtrRstLclCal;
		this.InitSeqControl_InitControlRstLclCal = this.InitSeqControl.InitControlRstLclCal;
		this.InitControlRstLclCal = this.InitSeqControl.InitControlRstLclCal;
		this.InitSeqControl_InhibitTxRdPtrRxReplLcdlInit = this.InitSeqControl.InhibitTxRdPtrRxReplLcdlInit;
		this.InhibitTxRdPtrRxReplLcdlInit = this.InitSeqControl.InhibitTxRdPtrRxReplLcdlInit;
		this.InitSeqControl_InitControlRxReplLcdlInit = this.InitSeqControl.InitControlRxReplLcdlInit;
		this.InitControlRxReplLcdlInit = this.InitSeqControl.InitControlRxReplLcdlInit;
		this.InitSeqControl_InhibitTxRdPtrTXFIFOInit = this.InitSeqControl.InhibitTxRdPtrTXFIFOInit;
		this.InhibitTxRdPtrTXFIFOInit = this.InitSeqControl.InhibitTxRdPtrTXFIFOInit;
		this.InitSeqControl_InitControlTXFIFOInit = this.InitSeqControl.InitControlTXFIFOInit;
		this.InitControlTXFIFOInit = this.InitSeqControl.InitControlTXFIFOInit;
		this.InitSeqControl_InhibitTxRdPtrDbDataPipeInit = this.InitSeqControl.InhibitTxRdPtrDbDataPipeInit;
		this.InhibitTxRdPtrDbDataPipeInit = this.InitSeqControl.InhibitTxRdPtrDbDataPipeInit;
		this.InitSeqControl_InhibitTxRdPtrDbRxEnPhUpdInit = this.InitSeqControl.InhibitTxRdPtrDbRxEnPhUpdInit;
		this.InhibitTxRdPtrDbRxEnPhUpdInit = this.InitSeqControl.InhibitTxRdPtrDbRxEnPhUpdInit;
		this.InitSeqControl_InitControlDbDataPipeInit = this.InitSeqControl.InitControlDbDataPipeInit;
		this.InitControlDbDataPipeInit = this.InitSeqControl.InitControlDbDataPipeInit;
		this.InitSeqControl_InhibitTxRdPtrDbPptInit = this.InitSeqControl.InhibitTxRdPtrDbPptInit;
		this.InhibitTxRdPtrDbPptInit = this.InitSeqControl.InhibitTxRdPtrDbPptInit;
		this.InitSeqControl_InitControlDbPptInit = this.InitSeqControl.InitControlDbPptInit;
		this.InitControlDbPptInit = this.InitSeqControl.InitControlDbPptInit;
		this.InitSeqControl_InitControlDbRxEnPhUpdInit = this.InitSeqControl.InitControlDbRxEnPhUpdInit;
		this.InitControlDbRxEnPhUpdInit = this.InitSeqControl.InitControlDbRxEnPhUpdInit;
		this.InitSeqControl_InhibitTxRdPtrRxReplSeqInit = this.InitSeqControl.InhibitTxRdPtrRxReplSeqInit;
		this.InhibitTxRdPtrRxReplSeqInit = this.InitSeqControl.InhibitTxRdPtrRxReplSeqInit;
		this.InitSeqControl_InitControlRxReplSeqInit = this.InitSeqControl.InitControlRxReplSeqInit;
		this.InitControlRxReplSeqInit = this.InitSeqControl.InitControlRxReplSeqInit;
		this.InitSeqControl_ReservedInitSeqControl = this.InitSeqControl.ReservedInitSeqControl;
		this.ReservedInitSeqControl = this.InitSeqControl.ReservedInitSeqControl;
      this.MtestMuxSel = ral_reg_DWC_DDRPHYA_AC1_p0_MtestMuxSel::type_id::create("MtestMuxSel",,get_full_name());
      if(this.MtestMuxSel.has_coverage(UVM_CVR_ALL))
      	this.MtestMuxSel.cg_bits.option.name = {get_name(), ".", "MtestMuxSel_bits"};
      this.MtestMuxSel.configure(this, null, "");
      this.MtestMuxSel.build();
      this.default_map.add_reg(this.MtestMuxSel, `UVM_REG_ADDR_WIDTH'h1A, "RW", 0);
		this.MtestMuxSel_MtestMuxSel = this.MtestMuxSel.MtestMuxSel;
      this.PorControl = ral_reg_DWC_DDRPHYA_AC1_p0_PorControl::type_id::create("PorControl",,get_full_name());
      if(this.PorControl.has_coverage(UVM_CVR_ALL))
      	this.PorControl.cg_bits.option.name = {get_name(), ".", "PorControl_bits"};
      this.PorControl.configure(this, null, "");
      this.PorControl.build();
      this.default_map.add_reg(this.PorControl, `UVM_REG_ADDR_WIDTH'h20, "RW", 0);
		this.PorControl_PwrOkDlyCtrl = this.PorControl.PwrOkDlyCtrl;
		this.PwrOkDlyCtrl = this.PorControl.PwrOkDlyCtrl;
      this.ClrPORMemReset = ral_reg_DWC_DDRPHYA_AC1_p0_ClrPORMemReset::type_id::create("ClrPORMemReset",,get_full_name());
      if(this.ClrPORMemReset.has_coverage(UVM_CVR_ALL))
      	this.ClrPORMemReset.cg_bits.option.name = {get_name(), ".", "ClrPORMemReset_bits"};
      this.ClrPORMemReset.configure(this, null, "");
      this.ClrPORMemReset.build();
      this.default_map.add_reg(this.ClrPORMemReset, `UVM_REG_ADDR_WIDTH'h21, "RW", 0);
		this.ClrPORMemReset_ClrPORMemReset = this.ClrPORMemReset.ClrPORMemReset;
      this.MemResetL = ral_reg_DWC_DDRPHYA_AC1_p0_MemResetL::type_id::create("MemResetL",,get_full_name());
      if(this.MemResetL.has_coverage(UVM_CVR_ALL))
      	this.MemResetL.cg_bits.option.name = {get_name(), ".", "MemResetL_bits"};
      this.MemResetL.configure(this, null, "");
      this.MemResetL.build();
      this.default_map.add_reg(this.MemResetL, `UVM_REG_ADDR_WIDTH'h22, "RW", 0);
		this.MemResetL_MemResetLValue = this.MemResetL.MemResetLValue;
		this.MemResetLValue = this.MemResetL.MemResetLValue;
		this.MemResetL_ProtectMemReset = this.MemResetL.ProtectMemReset;
		this.ProtectMemReset = this.MemResetL.ProtectMemReset;
		this.MemResetL_AsyncMemResetLRxMode = this.MemResetL.AsyncMemResetLRxMode;
		this.AsyncMemResetLRxMode = this.MemResetL.AsyncMemResetLRxMode;
      this.CMOSxHardMacroModeSel = ral_reg_DWC_DDRPHYA_AC1_p0_CMOSxHardMacroModeSel::type_id::create("CMOSxHardMacroModeSel",,get_full_name());
      if(this.CMOSxHardMacroModeSel.has_coverage(UVM_CVR_ALL))
      	this.CMOSxHardMacroModeSel.cg_bits.option.name = {get_name(), ".", "CMOSxHardMacroModeSel_bits"};
      this.CMOSxHardMacroModeSel.configure(this, null, "");
      this.CMOSxHardMacroModeSel.build();
      this.default_map.add_reg(this.CMOSxHardMacroModeSel, `UVM_REG_ADDR_WIDTH'h24, "RW", 0);
		this.CMOSxHardMacroModeSel_CMOSxHardMacroModeSel = this.CMOSxHardMacroModeSel.CMOSxHardMacroModeSel;
      this.RxAcVrefControl_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_RxAcVrefControl_p0::type_id::create("RxAcVrefControl_p0",,get_full_name());
      if(this.RxAcVrefControl_p0.has_coverage(UVM_CVR_ALL))
      	this.RxAcVrefControl_p0.cg_bits.option.name = {get_name(), ".", "RxAcVrefControl_p0_bits"};
      this.RxAcVrefControl_p0.configure(this, null, "");
      this.RxAcVrefControl_p0.build();
      this.default_map.add_reg(this.RxAcVrefControl_p0, `UVM_REG_ADDR_WIDTH'h25, "RW", 0);
		this.RxAcVrefControl_p0_RxAcVrefDac = this.RxAcVrefControl_p0.RxAcVrefDac;
		this.RxAcVrefDac = this.RxAcVrefControl_p0.RxAcVrefDac;
		this.RxAcVrefControl_p0_RxAcVrefDacEn = this.RxAcVrefControl_p0.RxAcVrefDacEn;
		this.RxAcVrefDacEn = this.RxAcVrefControl_p0.RxAcVrefDacEn;
      this.MemResetLStatus = ral_reg_DWC_DDRPHYA_AC1_p0_MemResetLStatus::type_id::create("MemResetLStatus",,get_full_name());
      if(this.MemResetLStatus.has_coverage(UVM_CVR_ALL))
      	this.MemResetLStatus.cg_bits.option.name = {get_name(), ".", "MemResetLStatus_bits"};
      this.MemResetLStatus.configure(this, null, "");
      this.MemResetLStatus.build();
      this.default_map.add_reg(this.MemResetLStatus, `UVM_REG_ADDR_WIDTH'h26, "RO", 0);
		this.MemResetLStatus_PORMemReset = this.MemResetLStatus.PORMemReset;
		this.PORMemReset = this.MemResetLStatus.PORMemReset;
		this.MemResetLStatus_AsyncMemResetLRxData = this.MemResetLStatus.AsyncMemResetLRxData;
		this.AsyncMemResetLRxData = this.MemResetLStatus.AsyncMemResetLRxData;
      this.ACDlyScaleGatingDisable = ral_reg_DWC_DDRPHYA_AC1_p0_ACDlyScaleGatingDisable::type_id::create("ACDlyScaleGatingDisable",,get_full_name());
      if(this.ACDlyScaleGatingDisable.has_coverage(UVM_CVR_ALL))
      	this.ACDlyScaleGatingDisable.cg_bits.option.name = {get_name(), ".", "ACDlyScaleGatingDisable_bits"};
      this.ACDlyScaleGatingDisable.configure(this, null, "");
      this.ACDlyScaleGatingDisable.build();
      this.default_map.add_reg(this.ACDlyScaleGatingDisable, `UVM_REG_ADDR_WIDTH'h27, "RW", 0);
		this.ACDlyScaleGatingDisable_ACDlyScaleGatingDisable = this.ACDlyScaleGatingDisable.ACDlyScaleGatingDisable;
      this.LcdlCalControl = ral_reg_DWC_DDRPHYA_AC1_p0_LcdlCalControl::type_id::create("LcdlCalControl",,get_full_name());
      if(this.LcdlCalControl.has_coverage(UVM_CVR_ALL))
      	this.LcdlCalControl.cg_bits.option.name = {get_name(), ".", "LcdlCalControl_bits"};
      this.LcdlCalControl.configure(this, null, "");
      this.LcdlCalControl.build();
      this.default_map.add_reg(this.LcdlCalControl, `UVM_REG_ADDR_WIDTH'h47, "RW", 0);
		this.LcdlCalControl_LcdlCalResetRelock = this.LcdlCalControl.LcdlCalResetRelock;
		this.LcdlCalResetRelock = this.LcdlCalControl.LcdlCalResetRelock;
		this.LcdlCalControl_LcdlCalStop = this.LcdlCalControl.LcdlCalStop;
		this.LcdlCalStop = this.LcdlCalControl.LcdlCalStop;
		this.LcdlCalControl_LcdlUpdTrackDis = this.LcdlCalControl.LcdlUpdTrackDis;
		this.LcdlUpdTrackDis = this.LcdlCalControl.LcdlUpdTrackDis;
      this.ACParityInvert = ral_reg_DWC_DDRPHYA_AC1_p0_ACParityInvert::type_id::create("ACParityInvert",,get_full_name());
      if(this.ACParityInvert.has_coverage(UVM_CVR_ALL))
      	this.ACParityInvert.cg_bits.option.name = {get_name(), ".", "ACParityInvert_bits"};
      this.ACParityInvert.configure(this, null, "");
      this.ACParityInvert.build();
      this.default_map.add_reg(this.ACParityInvert, `UVM_REG_ADDR_WIDTH'h4D, "RW", 0);
		this.ACParityInvert_ACParityInvert = this.ACParityInvert.ACParityInvert;
      this.ACPulseDllUpdatePhase = ral_reg_DWC_DDRPHYA_AC1_p0_ACPulseDllUpdatePhase::type_id::create("ACPulseDllUpdatePhase",,get_full_name());
      if(this.ACPulseDllUpdatePhase.has_coverage(UVM_CVR_ALL))
      	this.ACPulseDllUpdatePhase.cg_bits.option.name = {get_name(), ".", "ACPulseDllUpdatePhase_bits"};
      this.ACPulseDllUpdatePhase.configure(this, null, "");
      this.ACPulseDllUpdatePhase.build();
      this.default_map.add_reg(this.ACPulseDllUpdatePhase, `UVM_REG_ADDR_WIDTH'h79, "RW", 0);
		this.ACPulseDllUpdatePhase_ACPulseDllUpdatePhase = this.ACPulseDllUpdatePhase.ACPulseDllUpdatePhase;
      this.ScratchPadAC = ral_reg_DWC_DDRPHYA_AC1_p0_ScratchPadAC::type_id::create("ScratchPadAC",,get_full_name());
      if(this.ScratchPadAC.has_coverage(UVM_CVR_ALL))
      	this.ScratchPadAC.cg_bits.option.name = {get_name(), ".", "ScratchPadAC_bits"};
      this.ScratchPadAC.configure(this, null, "");
      this.ScratchPadAC.build();
      this.default_map.add_reg(this.ScratchPadAC, `UVM_REG_ADDR_WIDTH'h7D, "RW", 0);
		this.ScratchPadAC_ScratchPadAC = this.ScratchPadAC.ScratchPadAC;
      this.ATestMode = ral_reg_DWC_DDRPHYA_AC1_p0_ATestMode::type_id::create("ATestMode",,get_full_name());
      if(this.ATestMode.has_coverage(UVM_CVR_ALL))
      	this.ATestMode.cg_bits.option.name = {get_name(), ".", "ATestMode_bits"};
      this.ATestMode.configure(this, null, "");
      this.ATestMode.build();
      this.default_map.add_reg(this.ATestMode, `UVM_REG_ADDR_WIDTH'h7F, "RW", 0);
		this.ATestMode_ATestPrbsEn = this.ATestMode.ATestPrbsEn;
		this.ATestPrbsEn = this.ATestMode.ATestPrbsEn;
		this.ATestMode_ATestPrbs7or15Mode = this.ATestMode.ATestPrbs7or15Mode;
		this.ATestPrbs7or15Mode = this.ATestMode.ATestPrbs7or15Mode;
		this.ATestMode_ReservedATestMode42 = this.ATestMode.ReservedATestMode42;
		this.ReservedATestMode42 = this.ATestMode.ReservedATestMode42;
		this.ATestMode_ATestPrbsChkmode = this.ATestMode.ATestPrbsChkmode;
		this.ATestPrbsChkmode = this.ATestMode.ATestPrbsChkmode;
		this.ATestMode_PrbsDdrMode = this.ATestMode.PrbsDdrMode;
		this.PrbsDdrMode = this.ATestMode.PrbsDdrMode;
		this.ATestMode_ReservedATestMode7 = this.ATestMode.ReservedATestMode7;
		this.ReservedATestMode7 = this.ATestMode.ReservedATestMode7;
      this.AcDigStrobeGenSel = ral_reg_DWC_DDRPHYA_AC1_p0_AcDigStrobeGenSel::type_id::create("AcDigStrobeGenSel",,get_full_name());
      if(this.AcDigStrobeGenSel.has_coverage(UVM_CVR_ALL))
      	this.AcDigStrobeGenSel.cg_bits.option.name = {get_name(), ".", "AcDigStrobeGenSel_bits"};
      this.AcDigStrobeGenSel.configure(this, null, "");
      this.AcDigStrobeGenSel.build();
      this.default_map.add_reg(this.AcDigStrobeGenSel, `UVM_REG_ADDR_WIDTH'h86, "RW", 0);
		this.AcDigStrobeGenSel_AcDigStrobeGenSel = this.AcDigStrobeGenSel.AcDigStrobeGenSel;
      this.AcDigStrobePat = ral_reg_DWC_DDRPHYA_AC1_p0_AcDigStrobePat::type_id::create("AcDigStrobePat",,get_full_name());
      if(this.AcDigStrobePat.has_coverage(UVM_CVR_ALL))
      	this.AcDigStrobePat.cg_bits.option.name = {get_name(), ".", "AcDigStrobePat_bits"};
      this.AcDigStrobePat.configure(this, null, "");
      this.AcDigStrobePat.build();
      this.default_map.add_reg(this.AcDigStrobePat, `UVM_REG_ADDR_WIDTH'h87, "RW", 0);
		this.AcDigStrobePat_AcDigStrobePat = this.AcDigStrobePat.AcDigStrobePat;
      this.AcOdtEn = ral_reg_DWC_DDRPHYA_AC1_p0_AcOdtEn::type_id::create("AcOdtEn",,get_full_name());
      if(this.AcOdtEn.has_coverage(UVM_CVR_ALL))
      	this.AcOdtEn.cg_bits.option.name = {get_name(), ".", "AcOdtEn_bits"};
      this.AcOdtEn.configure(this, null, "");
      this.AcOdtEn.build();
      this.default_map.add_reg(this.AcOdtEn, `UVM_REG_ADDR_WIDTH'h88, "RW", 0);
		this.AcOdtEn_AcOdtEn = this.AcOdtEn.AcOdtEn;
      this.AcRxStrobeEnPat = ral_reg_DWC_DDRPHYA_AC1_p0_AcRxStrobeEnPat::type_id::create("AcRxStrobeEnPat",,get_full_name());
      if(this.AcRxStrobeEnPat.has_coverage(UVM_CVR_ALL))
      	this.AcRxStrobeEnPat.cg_bits.option.name = {get_name(), ".", "AcRxStrobeEnPat_bits"};
      this.AcRxStrobeEnPat.configure(this, null, "");
      this.AcRxStrobeEnPat.build();
      this.default_map.add_reg(this.AcRxStrobeEnPat, `UVM_REG_ADDR_WIDTH'h89, "RW", 0);
		this.AcRxStrobeEnPat_AcRxStrobeEnPat = this.AcRxStrobeEnPat.AcRxStrobeEnPat;
      this.ATxDlySelect_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ATxDlySelect_p0::type_id::create("ATxDlySelect_p0",,get_full_name());
      if(this.ATxDlySelect_p0.has_coverage(UVM_CVR_ALL))
      	this.ATxDlySelect_p0.cg_bits.option.name = {get_name(), ".", "ATxDlySelect_p0_bits"};
      this.ATxDlySelect_p0.configure(this, null, "");
      this.ATxDlySelect_p0.build();
      this.default_map.add_reg(this.ATxDlySelect_p0, `UVM_REG_ADDR_WIDTH'h8F, "RW", 0);
		this.ATxDlySelect_p0_ATxDlySelect_p0 = this.ATxDlySelect_p0.ATxDlySelect_p0;
      this.MapCA0toDfi = ral_reg_DWC_DDRPHYA_AC1_p0_MapCA0toDfi::type_id::create("MapCA0toDfi",,get_full_name());
      if(this.MapCA0toDfi.has_coverage(UVM_CVR_ALL))
      	this.MapCA0toDfi.cg_bits.option.name = {get_name(), ".", "MapCA0toDfi_bits"};
      this.MapCA0toDfi.configure(this, null, "");
      this.MapCA0toDfi.build();
      this.default_map.add_reg(this.MapCA0toDfi, `UVM_REG_ADDR_WIDTH'h90, "RW", 0);
		this.MapCA0toDfi_MapCA0toDfi = this.MapCA0toDfi.MapCA0toDfi;
      this.MapCA1toDfi = ral_reg_DWC_DDRPHYA_AC1_p0_MapCA1toDfi::type_id::create("MapCA1toDfi",,get_full_name());
      if(this.MapCA1toDfi.has_coverage(UVM_CVR_ALL))
      	this.MapCA1toDfi.cg_bits.option.name = {get_name(), ".", "MapCA1toDfi_bits"};
      this.MapCA1toDfi.configure(this, null, "");
      this.MapCA1toDfi.build();
      this.default_map.add_reg(this.MapCA1toDfi, `UVM_REG_ADDR_WIDTH'h91, "RW", 0);
		this.MapCA1toDfi_MapCA1toDfi = this.MapCA1toDfi.MapCA1toDfi;
      this.MapCA2toDfi = ral_reg_DWC_DDRPHYA_AC1_p0_MapCA2toDfi::type_id::create("MapCA2toDfi",,get_full_name());
      if(this.MapCA2toDfi.has_coverage(UVM_CVR_ALL))
      	this.MapCA2toDfi.cg_bits.option.name = {get_name(), ".", "MapCA2toDfi_bits"};
      this.MapCA2toDfi.configure(this, null, "");
      this.MapCA2toDfi.build();
      this.default_map.add_reg(this.MapCA2toDfi, `UVM_REG_ADDR_WIDTH'h92, "RW", 0);
		this.MapCA2toDfi_MapCA2toDfi = this.MapCA2toDfi.MapCA2toDfi;
      this.MapCA3toDfi = ral_reg_DWC_DDRPHYA_AC1_p0_MapCA3toDfi::type_id::create("MapCA3toDfi",,get_full_name());
      if(this.MapCA3toDfi.has_coverage(UVM_CVR_ALL))
      	this.MapCA3toDfi.cg_bits.option.name = {get_name(), ".", "MapCA3toDfi_bits"};
      this.MapCA3toDfi.configure(this, null, "");
      this.MapCA3toDfi.build();
      this.default_map.add_reg(this.MapCA3toDfi, `UVM_REG_ADDR_WIDTH'h93, "RW", 0);
		this.MapCA3toDfi_MapCA3toDfi = this.MapCA3toDfi.MapCA3toDfi;
      this.MapCA4toDfi = ral_reg_DWC_DDRPHYA_AC1_p0_MapCA4toDfi::type_id::create("MapCA4toDfi",,get_full_name());
      if(this.MapCA4toDfi.has_coverage(UVM_CVR_ALL))
      	this.MapCA4toDfi.cg_bits.option.name = {get_name(), ".", "MapCA4toDfi_bits"};
      this.MapCA4toDfi.configure(this, null, "");
      this.MapCA4toDfi.build();
      this.default_map.add_reg(this.MapCA4toDfi, `UVM_REG_ADDR_WIDTH'h94, "RW", 0);
		this.MapCA4toDfi_MapCA4toDfi = this.MapCA4toDfi.MapCA4toDfi;
      this.MapCA5toDfi = ral_reg_DWC_DDRPHYA_AC1_p0_MapCA5toDfi::type_id::create("MapCA5toDfi",,get_full_name());
      if(this.MapCA5toDfi.has_coverage(UVM_CVR_ALL))
      	this.MapCA5toDfi.cg_bits.option.name = {get_name(), ".", "MapCA5toDfi_bits"};
      this.MapCA5toDfi.configure(this, null, "");
      this.MapCA5toDfi.build();
      this.default_map.add_reg(this.MapCA5toDfi, `UVM_REG_ADDR_WIDTH'h95, "RW", 0);
		this.MapCA5toDfi_MapCA5toDfi = this.MapCA5toDfi.MapCA5toDfi;
      this.MapCA6toDfi = ral_reg_DWC_DDRPHYA_AC1_p0_MapCA6toDfi::type_id::create("MapCA6toDfi",,get_full_name());
      if(this.MapCA6toDfi.has_coverage(UVM_CVR_ALL))
      	this.MapCA6toDfi.cg_bits.option.name = {get_name(), ".", "MapCA6toDfi_bits"};
      this.MapCA6toDfi.configure(this, null, "");
      this.MapCA6toDfi.build();
      this.default_map.add_reg(this.MapCA6toDfi, `UVM_REG_ADDR_WIDTH'h96, "RW", 0);
		this.MapCA6toDfi_MapCA6toDfi = this.MapCA6toDfi.MapCA6toDfi;
      this.AsyncAcTxMode = ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcTxMode::type_id::create("AsyncAcTxMode",,get_full_name());
      if(this.AsyncAcTxMode.has_coverage(UVM_CVR_ALL))
      	this.AsyncAcTxMode.cg_bits.option.name = {get_name(), ".", "AsyncAcTxMode_bits"};
      this.AsyncAcTxMode.configure(this, null, "");
      this.AsyncAcTxMode.build();
      this.default_map.add_reg(this.AsyncAcTxMode, `UVM_REG_ADDR_WIDTH'hA0, "RW", 0);
		this.AsyncAcTxMode_AsyncAcTxMode = this.AsyncAcTxMode.AsyncAcTxMode;
      this.AsyncAcRxMode = ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcRxMode::type_id::create("AsyncAcRxMode",,get_full_name());
      if(this.AsyncAcRxMode.has_coverage(UVM_CVR_ALL))
      	this.AsyncAcRxMode.cg_bits.option.name = {get_name(), ".", "AsyncAcRxMode_bits"};
      this.AsyncAcRxMode.configure(this, null, "");
      this.AsyncAcRxMode.build();
      this.default_map.add_reg(this.AsyncAcRxMode, `UVM_REG_ADDR_WIDTH'hA1, "RW", 0);
		this.AsyncAcRxMode_AsyncAcRxMode = this.AsyncAcRxMode.AsyncAcRxMode;
      this.AsyncAcTxEn = ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcTxEn::type_id::create("AsyncAcTxEn",,get_full_name());
      if(this.AsyncAcTxEn.has_coverage(UVM_CVR_ALL))
      	this.AsyncAcTxEn.cg_bits.option.name = {get_name(), ".", "AsyncAcTxEn_bits"};
      this.AsyncAcTxEn.configure(this, null, "");
      this.AsyncAcTxEn.build();
      this.default_map.add_reg(this.AsyncAcTxEn, `UVM_REG_ADDR_WIDTH'hA2, "RW", 0);
		this.AsyncAcTxEn_AsyncAcTxEn = this.AsyncAcTxEn.AsyncAcTxEn;
      this.AsyncAcTxData = ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcTxData::type_id::create("AsyncAcTxData",,get_full_name());
      if(this.AsyncAcTxData.has_coverage(UVM_CVR_ALL))
      	this.AsyncAcTxData.cg_bits.option.name = {get_name(), ".", "AsyncAcTxData_bits"};
      this.AsyncAcTxData.configure(this, null, "");
      this.AsyncAcTxData.build();
      this.default_map.add_reg(this.AsyncAcTxData, `UVM_REG_ADDR_WIDTH'hA3, "RW", 0);
		this.AsyncAcTxData_AsyncAcTxData = this.AsyncAcTxData.AsyncAcTxData;
      this.AsyncAcRxData = ral_reg_DWC_DDRPHYA_AC1_p0_AsyncAcRxData::type_id::create("AsyncAcRxData",,get_full_name());
      if(this.AsyncAcRxData.has_coverage(UVM_CVR_ALL))
      	this.AsyncAcRxData.cg_bits.option.name = {get_name(), ".", "AsyncAcRxData_bits"};
      this.AsyncAcRxData.configure(this, null, "");
      this.AsyncAcRxData.build();
      this.default_map.add_reg(this.AsyncAcRxData, `UVM_REG_ADDR_WIDTH'hA5, "RO", 0);
		this.AsyncAcRxData_AsyncAcRxData = this.AsyncAcRxData.AsyncAcRxData;
      this.ForceClkDisable = ral_reg_DWC_DDRPHYA_AC1_p0_ForceClkDisable::type_id::create("ForceClkDisable",,get_full_name());
      if(this.ForceClkDisable.has_coverage(UVM_CVR_ALL))
      	this.ForceClkDisable.cg_bits.option.name = {get_name(), ".", "ForceClkDisable_bits"};
      this.ForceClkDisable.configure(this, null, "");
      this.ForceClkDisable.build();
      this.default_map.add_reg(this.ForceClkDisable, `UVM_REG_ADDR_WIDTH'hA6, "RW", 0);
		this.ForceClkDisable_ForceClkDisable = this.ForceClkDisable.ForceClkDisable;
      this.CaBusTriEn = ral_reg_DWC_DDRPHYA_AC1_p0_CaBusTriEn::type_id::create("CaBusTriEn",,get_full_name());
      if(this.CaBusTriEn.has_coverage(UVM_CVR_ALL))
      	this.CaBusTriEn.cg_bits.option.name = {get_name(), ".", "CaBusTriEn_bits"};
      this.CaBusTriEn.configure(this, null, "");
      this.CaBusTriEn.build();
      this.default_map.add_reg(this.CaBusTriEn, `UVM_REG_ADDR_WIDTH'hAB, "RW", 0);
		this.CaBusTriEn_CaBusTriEn = this.CaBusTriEn.CaBusTriEn;
      this.AcLnDisable = ral_reg_DWC_DDRPHYA_AC1_p0_AcLnDisable::type_id::create("AcLnDisable",,get_full_name());
      if(this.AcLnDisable.has_coverage(UVM_CVR_ALL))
      	this.AcLnDisable.cg_bits.option.name = {get_name(), ".", "AcLnDisable_bits"};
      this.AcLnDisable.configure(this, null, "");
      this.AcLnDisable.build();
      this.default_map.add_reg(this.AcLnDisable, `UVM_REG_ADDR_WIDTH'hAC, "RW", 0);
		this.AcLnDisable_AcLnDisable = this.AcLnDisable.AcLnDisable;
      this.DfiClkAcLnDis = ral_reg_DWC_DDRPHYA_AC1_p0_DfiClkAcLnDis::type_id::create("DfiClkAcLnDis",,get_full_name());
      if(this.DfiClkAcLnDis.has_coverage(UVM_CVR_ALL))
      	this.DfiClkAcLnDis.cg_bits.option.name = {get_name(), ".", "DfiClkAcLnDis_bits"};
      this.DfiClkAcLnDis.configure(this, null, "");
      this.DfiClkAcLnDis.build();
      this.default_map.add_reg(this.DfiClkAcLnDis, `UVM_REG_ADDR_WIDTH'hAD, "RW", 0);
		this.DfiClkAcLnDis_DfiClkAcLnDis = this.DfiClkAcLnDis.DfiClkAcLnDis;
      this.PClkAcLnDis = ral_reg_DWC_DDRPHYA_AC1_p0_PClkAcLnDis::type_id::create("PClkAcLnDis",,get_full_name());
      if(this.PClkAcLnDis.has_coverage(UVM_CVR_ALL))
      	this.PClkAcLnDis.cg_bits.option.name = {get_name(), ".", "PClkAcLnDis_bits"};
      this.PClkAcLnDis.configure(this, null, "");
      this.PClkAcLnDis.build();
      this.default_map.add_reg(this.PClkAcLnDis, `UVM_REG_ADDR_WIDTH'hAE, "RW", 0);
		this.PClkAcLnDis_PClkAcLnDis = this.PClkAcLnDis.PClkAcLnDis;
      this.AcLcdlCalPhDetOut = ral_reg_DWC_DDRPHYA_AC1_p0_AcLcdlCalPhDetOut::type_id::create("AcLcdlCalPhDetOut",,get_full_name());
      if(this.AcLcdlCalPhDetOut.has_coverage(UVM_CVR_ALL))
      	this.AcLcdlCalPhDetOut.cg_bits.option.name = {get_name(), ".", "AcLcdlCalPhDetOut_bits"};
      this.AcLcdlCalPhDetOut.configure(this, null, "");
      this.AcLcdlCalPhDetOut.build();
      this.default_map.add_reg(this.AcLcdlCalPhDetOut, `UVM_REG_ADDR_WIDTH'hAF, "RO", 0);
		this.AcLcdlCalPhDetOut_AcLcdlCalPhDetOut = this.AcLcdlCalPhDetOut.AcLcdlCalPhDetOut;
      this.ACXTxDly_r0_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r0_p0::type_id::create("ACXTxDly_r0_p0",,get_full_name());
      if(this.ACXTxDly_r0_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly_r0_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDly_r0_p0_bits"};
      this.ACXTxDly_r0_p0.configure(this, null, "");
      this.ACXTxDly_r0_p0.build();
      this.default_map.add_reg(this.ACXTxDly_r0_p0, `UVM_REG_ADDR_WIDTH'hD8, "RW", 0);
		this.ACXTxDly_r0_p0_ACXTxDly_r0_p0 = this.ACXTxDly_r0_p0.ACXTxDly_r0_p0;
      this.CKXTxDly_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_CKXTxDly_p0::type_id::create("CKXTxDly_p0",,get_full_name());
      if(this.CKXTxDly_p0.has_coverage(UVM_CVR_ALL))
      	this.CKXTxDly_p0.cg_bits.option.name = {get_name(), ".", "CKXTxDly_p0_bits"};
      this.CKXTxDly_p0.configure(this, null, "");
      this.CKXTxDly_p0.build();
      this.default_map.add_reg(this.CKXTxDly_p0, `UVM_REG_ADDR_WIDTH'hD9, "RW", 0);
		this.CKXTxDly_p0_CKXTxDly_p0 = this.CKXTxDly_p0.CKXTxDly_p0;
      this.ACXTxDlyDTO_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDlyDTO_p0::type_id::create("ACXTxDlyDTO_p0",,get_full_name());
      if(this.ACXTxDlyDTO_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDlyDTO_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDlyDTO_p0_bits"};
      this.ACXTxDlyDTO_p0.configure(this, null, "");
      this.ACXTxDlyDTO_p0.build();
      this.default_map.add_reg(this.ACXTxDlyDTO_p0, `UVM_REG_ADDR_WIDTH'hDA, "RW", 0);
		this.ACXTxDlyDTO_p0_ACXTxDlyDTO_p0 = this.ACXTxDlyDTO_p0.ACXTxDlyDTO_p0;
      this.ACXTxDly2nMode_r0_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r0_p0::type_id::create("ACXTxDly2nMode_r0_p0",,get_full_name());
      if(this.ACXTxDly2nMode_r0_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly2nMode_r0_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDly2nMode_r0_p0_bits"};
      this.ACXTxDly2nMode_r0_p0.configure(this, null, "");
      this.ACXTxDly2nMode_r0_p0.build();
      this.default_map.add_reg(this.ACXTxDly2nMode_r0_p0, `UVM_REG_ADDR_WIDTH'hDE, "RW", 0);
		this.ACXTxDly2nMode_r0_p0_ACXTxDly2nMode_r0_p0 = this.ACXTxDly2nMode_r0_p0.ACXTxDly2nMode_r0_p0;
      this.AcLcdlUpdInterval_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_AcLcdlUpdInterval_p0::type_id::create("AcLcdlUpdInterval_p0",,get_full_name());
      if(this.AcLcdlUpdInterval_p0.has_coverage(UVM_CVR_ALL))
      	this.AcLcdlUpdInterval_p0.cg_bits.option.name = {get_name(), ".", "AcLcdlUpdInterval_p0_bits"};
      this.AcLcdlUpdInterval_p0.configure(this, null, "");
      this.AcLcdlUpdInterval_p0.build();
      this.default_map.add_reg(this.AcLcdlUpdInterval_p0, `UVM_REG_ADDR_WIDTH'hEB, "RW", 0);
		this.AcLcdlUpdInterval_p0_AcLcdlUpdInterval_p0 = this.AcLcdlUpdInterval_p0.AcLcdlUpdInterval_p0;
      this.LcdlCalSeqUpdCK_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_LcdlCalSeqUpdCK_p0::type_id::create("LcdlCalSeqUpdCK_p0",,get_full_name());
      if(this.LcdlCalSeqUpdCK_p0.has_coverage(UVM_CVR_ALL))
      	this.LcdlCalSeqUpdCK_p0.cg_bits.option.name = {get_name(), ".", "LcdlCalSeqUpdCK_p0_bits"};
      this.LcdlCalSeqUpdCK_p0.configure(this, null, "");
      this.LcdlCalSeqUpdCK_p0.build();
      this.default_map.add_reg(this.LcdlCalSeqUpdCK_p0, `UVM_REG_ADDR_WIDTH'hEC, "RW", 0);
		this.LcdlCalSeqUpdCK_p0_LcdlCalSeqUpdCK_p0 = this.LcdlCalSeqUpdCK_p0.LcdlCalSeqUpdCK_p0;
      this.CkTriEn = ral_reg_DWC_DDRPHYA_AC1_p0_CkTriEn::type_id::create("CkTriEn",,get_full_name());
      if(this.CkTriEn.has_coverage(UVM_CVR_ALL))
      	this.CkTriEn.cg_bits.option.name = {get_name(), ".", "CkTriEn_bits"};
      this.CkTriEn.configure(this, null, "");
      this.CkTriEn.build();
      this.default_map.add_reg(this.CkTriEn, `UVM_REG_ADDR_WIDTH'hED, "RW", 0);
		this.CkTriEn_CkTriEn = this.CkTriEn.CkTriEn;
      this.ACReserved0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACReserved0::type_id::create("ACReserved0",,get_full_name());
      if(this.ACReserved0.has_coverage(UVM_CVR_ALL))
      	this.ACReserved0.cg_bits.option.name = {get_name(), ".", "ACReserved0_bits"};
      this.ACReserved0.configure(this, null, "");
      this.ACReserved0.build();
      this.default_map.add_reg(this.ACReserved0, `UVM_REG_ADDR_WIDTH'hF9, "RW", 0);
		this.ACReserved0_ACReserved0 = this.ACReserved0.ACReserved0;
      this.LcdlCalCtrl = ral_reg_DWC_DDRPHYA_AC1_p0_LcdlCalCtrl::type_id::create("LcdlCalCtrl",,get_full_name());
      if(this.LcdlCalCtrl.has_coverage(UVM_CVR_ALL))
      	this.LcdlCalCtrl.cg_bits.option.name = {get_name(), ".", "LcdlCalCtrl_bits"};
      this.LcdlCalCtrl.configure(this, null, "");
      this.LcdlCalCtrl.build();
      this.default_map.add_reg(this.LcdlCalCtrl, `UVM_REG_ADDR_WIDTH'hFE, "RW", 0);
		this.LcdlCalCtrl_LcdlCalCtrl = this.LcdlCalCtrl.LcdlCalCtrl;
      this.PUBReservedP1_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_PUBReservedP1_p0::type_id::create("PUBReservedP1_p0",,get_full_name());
      if(this.PUBReservedP1_p0.has_coverage(UVM_CVR_ALL))
      	this.PUBReservedP1_p0.cg_bits.option.name = {get_name(), ".", "PUBReservedP1_p0_bits"};
      this.PUBReservedP1_p0.configure(this, null, "");
      this.PUBReservedP1_p0.build();
      this.default_map.add_reg(this.PUBReservedP1_p0, `UVM_REG_ADDR_WIDTH'hFF, "RW", 0);
		this.PUBReservedP1_p0_PUBReservedP1_p0 = this.PUBReservedP1_p0.PUBReservedP1_p0;
      this.PclkDCDCtrl_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCDCtrl_p0::type_id::create("PclkDCDCtrl_p0",,get_full_name());
      if(this.PclkDCDCtrl_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCDCtrl_p0.cg_bits.option.name = {get_name(), ".", "PclkDCDCtrl_p0_bits"};
      this.PclkDCDCtrl_p0.configure(this, null, "");
      this.PclkDCDCtrl_p0.build();
      this.default_map.add_reg(this.PclkDCDCtrl_p0, `UVM_REG_ADDR_WIDTH'h100, "RW", 0);
		this.PclkDCDCtrl_p0_PclkDCDEn = this.PclkDCDCtrl_p0.PclkDCDEn;
		this.PclkDCDEn = this.PclkDCDCtrl_p0.PclkDCDEn;
		this.PclkDCDCtrl_p0_PclkDCDOffsetMode = this.PclkDCDCtrl_p0.PclkDCDOffsetMode;
		this.PclkDCDOffsetMode = this.PclkDCDCtrl_p0.PclkDCDOffsetMode;
      this.ForceInternalUpdate = ral_reg_DWC_DDRPHYA_AC1_p0_ForceInternalUpdate::type_id::create("ForceInternalUpdate",,get_full_name());
      if(this.ForceInternalUpdate.has_coverage(UVM_CVR_ALL))
      	this.ForceInternalUpdate.cg_bits.option.name = {get_name(), ".", "ForceInternalUpdate_bits"};
      this.ForceInternalUpdate.configure(this, null, "");
      this.ForceInternalUpdate.build();
      this.default_map.add_reg(this.ForceInternalUpdate, `UVM_REG_ADDR_WIDTH'h103, "RW", 0);
		this.ForceInternalUpdate_ForceInternalUpdate = this.ForceInternalUpdate.ForceInternalUpdate;
      this.ATestPrbsErrCntSEC0 = ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSEC0::type_id::create("ATestPrbsErrCntSEC0",,get_full_name());
      if(this.ATestPrbsErrCntSEC0.has_coverage(UVM_CVR_ALL))
      	this.ATestPrbsErrCntSEC0.cg_bits.option.name = {get_name(), ".", "ATestPrbsErrCntSEC0_bits"};
      this.ATestPrbsErrCntSEC0.configure(this, null, "");
      this.ATestPrbsErrCntSEC0.build();
      this.default_map.add_reg(this.ATestPrbsErrCntSEC0, `UVM_REG_ADDR_WIDTH'h1A8, "RO", 0);
		this.ATestPrbsErrCntSEC0_ATestPrbsErrCntSEC0 = this.ATestPrbsErrCntSEC0.ATestPrbsErrCntSEC0;
      this.ATestPrbsErrCntSEC1 = ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSEC1::type_id::create("ATestPrbsErrCntSEC1",,get_full_name());
      if(this.ATestPrbsErrCntSEC1.has_coverage(UVM_CVR_ALL))
      	this.ATestPrbsErrCntSEC1.cg_bits.option.name = {get_name(), ".", "ATestPrbsErrCntSEC1_bits"};
      this.ATestPrbsErrCntSEC1.configure(this, null, "");
      this.ATestPrbsErrCntSEC1.build();
      this.default_map.add_reg(this.ATestPrbsErrCntSEC1, `UVM_REG_ADDR_WIDTH'h1A9, "RO", 0);
		this.ATestPrbsErrCntSEC1_ATestPrbsErrCntSEC1 = this.ATestPrbsErrCntSEC1.ATestPrbsErrCntSEC1;
      this.AcPDsampleSEC0 = ral_reg_DWC_DDRPHYA_AC1_p0_AcPDsampleSEC0::type_id::create("AcPDsampleSEC0",,get_full_name());
      if(this.AcPDsampleSEC0.has_coverage(UVM_CVR_ALL))
      	this.AcPDsampleSEC0.cg_bits.option.name = {get_name(), ".", "AcPDsampleSEC0_bits"};
      this.AcPDsampleSEC0.configure(this, null, "");
      this.AcPDsampleSEC0.build();
      this.default_map.add_reg(this.AcPDsampleSEC0, `UVM_REG_ADDR_WIDTH'h1B8, "RO", 0);
		this.AcPDsampleSEC0_AcPDsampleSEC0 = this.AcPDsampleSEC0.AcPDsampleSEC0;
      this.AcPDsampleSEC1 = ral_reg_DWC_DDRPHYA_AC1_p0_AcPDsampleSEC1::type_id::create("AcPDsampleSEC1",,get_full_name());
      if(this.AcPDsampleSEC1.has_coverage(UVM_CVR_ALL))
      	this.AcPDsampleSEC1.cg_bits.option.name = {get_name(), ".", "AcPDsampleSEC1_bits"};
      this.AcPDsampleSEC1.configure(this, null, "");
      this.AcPDsampleSEC1.build();
      this.default_map.add_reg(this.AcPDsampleSEC1, `UVM_REG_ADDR_WIDTH'h1B9, "RO", 0);
		this.AcPDsampleSEC1_AcPDsampleSEC1 = this.AcPDsampleSEC1.AcPDsampleSEC1;
      this.AcPDsampleDIFF = ral_reg_DWC_DDRPHYA_AC1_p0_AcPDsampleDIFF::type_id::create("AcPDsampleDIFF",,get_full_name());
      if(this.AcPDsampleDIFF.has_coverage(UVM_CVR_ALL))
      	this.AcPDsampleDIFF.cg_bits.option.name = {get_name(), ".", "AcPDsampleDIFF_bits"};
      this.AcPDsampleDIFF.configure(this, null, "");
      this.AcPDsampleDIFF.build();
      this.default_map.add_reg(this.AcPDsampleDIFF, `UVM_REG_ADDR_WIDTH'h1CA, "RO", 0);
		this.AcPDsampleDIFF_PDsampleT = this.AcPDsampleDIFF.PDsampleT;
		this.PDsampleT = this.AcPDsampleDIFF.PDsampleT;
		this.AcPDsampleDIFF_PDsampleC = this.AcPDsampleDIFF.PDsampleC;
		this.PDsampleC = this.AcPDsampleDIFF.PDsampleC;
      this.ACXTxDly_r1_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r1_p0::type_id::create("ACXTxDly_r1_p0",,get_full_name());
      if(this.ACXTxDly_r1_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly_r1_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDly_r1_p0_bits"};
      this.ACXTxDly_r1_p0.configure(this, null, "");
      this.ACXTxDly_r1_p0.build();
      this.default_map.add_reg(this.ACXTxDly_r1_p0, `UVM_REG_ADDR_WIDTH'h1D8, "RW", 0);
		this.ACXTxDly_r1_p0_ACXTxDly_r1_p0 = this.ACXTxDly_r1_p0.ACXTxDly_r1_p0;
      this.ACXTxDly2nMode_r1_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r1_p0::type_id::create("ACXTxDly2nMode_r1_p0",,get_full_name());
      if(this.ACXTxDly2nMode_r1_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly2nMode_r1_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDly2nMode_r1_p0_bits"};
      this.ACXTxDly2nMode_r1_p0.configure(this, null, "");
      this.ACXTxDly2nMode_r1_p0.build();
      this.default_map.add_reg(this.ACXTxDly2nMode_r1_p0, `UVM_REG_ADDR_WIDTH'h1DE, "RW", 0);
		this.ACXTxDly2nMode_r1_p0_ACXTxDly2nMode_r1_p0 = this.ACXTxDly2nMode_r1_p0.ACXTxDly2nMode_r1_p0;
      this.ACXTxDly_r2_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r2_p0::type_id::create("ACXTxDly_r2_p0",,get_full_name());
      if(this.ACXTxDly_r2_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly_r2_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDly_r2_p0_bits"};
      this.ACXTxDly_r2_p0.configure(this, null, "");
      this.ACXTxDly_r2_p0.build();
      this.default_map.add_reg(this.ACXTxDly_r2_p0, `UVM_REG_ADDR_WIDTH'h2D8, "RW", 0);
		this.ACXTxDly_r2_p0_ACXTxDly_r2_p0 = this.ACXTxDly_r2_p0.ACXTxDly_r2_p0;
      this.ACXTxDly2nMode_r2_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r2_p0::type_id::create("ACXTxDly2nMode_r2_p0",,get_full_name());
      if(this.ACXTxDly2nMode_r2_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly2nMode_r2_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDly2nMode_r2_p0_bits"};
      this.ACXTxDly2nMode_r2_p0.configure(this, null, "");
      this.ACXTxDly2nMode_r2_p0.build();
      this.default_map.add_reg(this.ACXTxDly2nMode_r2_p0, `UVM_REG_ADDR_WIDTH'h2DE, "RW", 0);
		this.ACXTxDly2nMode_r2_p0_ACXTxDly2nMode_r2_p0 = this.ACXTxDly2nMode_r2_p0.ACXTxDly2nMode_r2_p0;
      this.ACXTxDly_r3_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r3_p0::type_id::create("ACXTxDly_r3_p0",,get_full_name());
      if(this.ACXTxDly_r3_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly_r3_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDly_r3_p0_bits"};
      this.ACXTxDly_r3_p0.configure(this, null, "");
      this.ACXTxDly_r3_p0.build();
      this.default_map.add_reg(this.ACXTxDly_r3_p0, `UVM_REG_ADDR_WIDTH'h3D8, "RW", 0);
		this.ACXTxDly_r3_p0_ACXTxDly_r3_p0 = this.ACXTxDly_r3_p0.ACXTxDly_r3_p0;
      this.ACXTxDly2nMode_r3_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r3_p0::type_id::create("ACXTxDly2nMode_r3_p0",,get_full_name());
      if(this.ACXTxDly2nMode_r3_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly2nMode_r3_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDly2nMode_r3_p0_bits"};
      this.ACXTxDly2nMode_r3_p0.configure(this, null, "");
      this.ACXTxDly2nMode_r3_p0.build();
      this.default_map.add_reg(this.ACXTxDly2nMode_r3_p0, `UVM_REG_ADDR_WIDTH'h3DE, "RW", 0);
		this.ACXTxDly2nMode_r3_p0_ACXTxDly2nMode_r3_p0 = this.ACXTxDly2nMode_r3_p0.ACXTxDly2nMode_r3_p0;
      this.ATestPrbsErrCntDIFF0T = ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntDIFF0T::type_id::create("ATestPrbsErrCntDIFF0T",,get_full_name());
      if(this.ATestPrbsErrCntDIFF0T.has_coverage(UVM_CVR_ALL))
      	this.ATestPrbsErrCntDIFF0T.cg_bits.option.name = {get_name(), ".", "ATestPrbsErrCntDIFF0T_bits"};
      this.ATestPrbsErrCntDIFF0T.configure(this, null, "");
      this.ATestPrbsErrCntDIFF0T.build();
      this.default_map.add_reg(this.ATestPrbsErrCntDIFF0T, `UVM_REG_ADDR_WIDTH'h3E0, "RO", 0);
		this.ATestPrbsErrCntDIFF0T_ATestPrbsErrCntDIFF0T = this.ATestPrbsErrCntDIFF0T.ATestPrbsErrCntDIFF0T;
      this.ATestPrbsErrCntDIFF0C = ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntDIFF0C::type_id::create("ATestPrbsErrCntDIFF0C",,get_full_name());
      if(this.ATestPrbsErrCntDIFF0C.has_coverage(UVM_CVR_ALL))
      	this.ATestPrbsErrCntDIFF0C.cg_bits.option.name = {get_name(), ".", "ATestPrbsErrCntDIFF0C_bits"};
      this.ATestPrbsErrCntDIFF0C.configure(this, null, "");
      this.ATestPrbsErrCntDIFF0C.build();
      this.default_map.add_reg(this.ATestPrbsErrCntDIFF0C, `UVM_REG_ADDR_WIDTH'h3E4, "RO", 0);
		this.ATestPrbsErrCntDIFF0C_ATestPrbsErrCntDIFF0C = this.ATestPrbsErrCntDIFF0C.ATestPrbsErrCntDIFF0C;
      this.ACXTxDly_r4_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r4_p0::type_id::create("ACXTxDly_r4_p0",,get_full_name());
      if(this.ACXTxDly_r4_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly_r4_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDly_r4_p0_bits"};
      this.ACXTxDly_r4_p0.configure(this, null, "");
      this.ACXTxDly_r4_p0.build();
      this.default_map.add_reg(this.ACXTxDly_r4_p0, `UVM_REG_ADDR_WIDTH'h4D8, "RW", 0);
		this.ACXTxDly_r4_p0_ACXTxDly_r4_p0 = this.ACXTxDly_r4_p0.ACXTxDly_r4_p0;
      this.ACXTxDly2nMode_r4_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r4_p0::type_id::create("ACXTxDly2nMode_r4_p0",,get_full_name());
      if(this.ACXTxDly2nMode_r4_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly2nMode_r4_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDly2nMode_r4_p0_bits"};
      this.ACXTxDly2nMode_r4_p0.configure(this, null, "");
      this.ACXTxDly2nMode_r4_p0.build();
      this.default_map.add_reg(this.ACXTxDly2nMode_r4_p0, `UVM_REG_ADDR_WIDTH'h4DE, "RW", 0);
		this.ACXTxDly2nMode_r4_p0_ACXTxDly2nMode_r4_p0 = this.ACXTxDly2nMode_r4_p0.ACXTxDly2nMode_r4_p0;
      this.ACXTxDly_r5_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r5_p0::type_id::create("ACXTxDly_r5_p0",,get_full_name());
      if(this.ACXTxDly_r5_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly_r5_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDly_r5_p0_bits"};
      this.ACXTxDly_r5_p0.configure(this, null, "");
      this.ACXTxDly_r5_p0.build();
      this.default_map.add_reg(this.ACXTxDly_r5_p0, `UVM_REG_ADDR_WIDTH'h5D8, "RW", 0);
		this.ACXTxDly_r5_p0_ACXTxDly_r5_p0 = this.ACXTxDly_r5_p0.ACXTxDly_r5_p0;
      this.ACXTxDly2nMode_r5_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r5_p0::type_id::create("ACXTxDly2nMode_r5_p0",,get_full_name());
      if(this.ACXTxDly2nMode_r5_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly2nMode_r5_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDly2nMode_r5_p0_bits"};
      this.ACXTxDly2nMode_r5_p0.configure(this, null, "");
      this.ACXTxDly2nMode_r5_p0.build();
      this.default_map.add_reg(this.ACXTxDly2nMode_r5_p0, `UVM_REG_ADDR_WIDTH'h5DE, "RW", 0);
		this.ACXTxDly2nMode_r5_p0_ACXTxDly2nMode_r5_p0 = this.ACXTxDly2nMode_r5_p0.ACXTxDly2nMode_r5_p0;
      this.ACXTxDly_r6_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r6_p0::type_id::create("ACXTxDly_r6_p0",,get_full_name());
      if(this.ACXTxDly_r6_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly_r6_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDly_r6_p0_bits"};
      this.ACXTxDly_r6_p0.configure(this, null, "");
      this.ACXTxDly_r6_p0.build();
      this.default_map.add_reg(this.ACXTxDly_r6_p0, `UVM_REG_ADDR_WIDTH'h6D8, "RW", 0);
		this.ACXTxDly_r6_p0_ACXTxDly_r6_p0 = this.ACXTxDly_r6_p0.ACXTxDly_r6_p0;
      this.ACXTxDly2nMode_r6_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r6_p0::type_id::create("ACXTxDly2nMode_r6_p0",,get_full_name());
      if(this.ACXTxDly2nMode_r6_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly2nMode_r6_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDly2nMode_r6_p0_bits"};
      this.ACXTxDly2nMode_r6_p0.configure(this, null, "");
      this.ACXTxDly2nMode_r6_p0.build();
      this.default_map.add_reg(this.ACXTxDly2nMode_r6_p0, `UVM_REG_ADDR_WIDTH'h6DE, "RW", 0);
		this.ACXTxDly2nMode_r6_p0_ACXTxDly2nMode_r6_p0 = this.ACXTxDly2nMode_r6_p0.ACXTxDly2nMode_r6_p0;
      this.ACXTxDly_r7_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r7_p0::type_id::create("ACXTxDly_r7_p0",,get_full_name());
      if(this.ACXTxDly_r7_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly_r7_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDly_r7_p0_bits"};
      this.ACXTxDly_r7_p0.configure(this, null, "");
      this.ACXTxDly_r7_p0.build();
      this.default_map.add_reg(this.ACXTxDly_r7_p0, `UVM_REG_ADDR_WIDTH'h7D8, "RW", 0);
		this.ACXTxDly_r7_p0_ACXTxDly_r7_p0 = this.ACXTxDly_r7_p0.ACXTxDly_r7_p0;
      this.ACXTxDly2nMode_r7_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r7_p0::type_id::create("ACXTxDly2nMode_r7_p0",,get_full_name());
      if(this.ACXTxDly2nMode_r7_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly2nMode_r7_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDly2nMode_r7_p0_bits"};
      this.ACXTxDly2nMode_r7_p0.configure(this, null, "");
      this.ACXTxDly2nMode_r7_p0.build();
      this.default_map.add_reg(this.ACXTxDly2nMode_r7_p0, `UVM_REG_ADDR_WIDTH'h7DE, "RW", 0);
		this.ACXTxDly2nMode_r7_p0_ACXTxDly2nMode_r7_p0 = this.ACXTxDly2nMode_r7_p0.ACXTxDly2nMode_r7_p0;
      this.PclkDCACalCtrl0AC = ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCACalCtrl0AC::type_id::create("PclkDCACalCtrl0AC",,get_full_name());
      if(this.PclkDCACalCtrl0AC.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACalCtrl0AC.cg_bits.option.name = {get_name(), ".", "PclkDCACalCtrl0AC_bits"};
      this.PclkDCACalCtrl0AC.configure(this, null, "");
      this.PclkDCACalCtrl0AC.build();
      this.default_map.add_reg(this.PclkDCACalCtrl0AC, `UVM_REG_ADDR_WIDTH'h800, "RW", 0);
		this.PclkDCACalCtrl0AC_PclkDCAIncOnHiAC = this.PclkDCACalCtrl0AC.PclkDCAIncOnHiAC;
		this.PclkDCAIncOnHiAC = this.PclkDCACalCtrl0AC.PclkDCAIncOnHiAC;
		this.PclkDCACalCtrl0AC_PclkDCAIncOnLoAC = this.PclkDCACalCtrl0AC.PclkDCAIncOnLoAC;
		this.PclkDCAIncOnLoAC = this.PclkDCACalCtrl0AC.PclkDCAIncOnLoAC;
		this.PclkDCACalCtrl0AC_PclkDCADecOnHiAC = this.PclkDCACalCtrl0AC.PclkDCADecOnHiAC;
		this.PclkDCADecOnHiAC = this.PclkDCACalCtrl0AC.PclkDCADecOnHiAC;
		this.PclkDCACalCtrl0AC_PclkDCADecOnLoAC = this.PclkDCACalCtrl0AC.PclkDCADecOnLoAC;
		this.PclkDCADecOnLoAC = this.PclkDCACalCtrl0AC.PclkDCADecOnLoAC;
      this.PclkDCADynCtrl = ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCADynCtrl::type_id::create("PclkDCADynCtrl",,get_full_name());
      if(this.PclkDCADynCtrl.has_coverage(UVM_CVR_ALL))
      	this.PclkDCADynCtrl.cg_bits.option.name = {get_name(), ".", "PclkDCADynCtrl_bits"};
      this.PclkDCADynCtrl.configure(this, null, "");
      this.PclkDCADynCtrl.build();
      this.default_map.add_reg(this.PclkDCADynCtrl, `UVM_REG_ADDR_WIDTH'h802, "RW", 0);
		this.PclkDCADynCtrl_PclkDCACalReset = this.PclkDCADynCtrl.PclkDCACalReset;
		this.PclkDCACalReset = this.PclkDCADynCtrl.PclkDCACalReset;
		this.PclkDCADynCtrl_PclkDCAQuickSearch = this.PclkDCADynCtrl.PclkDCAQuickSearch;
		this.PclkDCAQuickSearch = this.PclkDCADynCtrl.PclkDCAQuickSearch;
		this.PclkDCADynCtrl_PclkDCAForceSampVld = this.PclkDCADynCtrl.PclkDCAForceSampVld;
		this.PclkDCAForceSampVld = this.PclkDCADynCtrl.PclkDCAForceSampVld;
		this.PclkDCADynCtrl_PclkDCAForceUpd = this.PclkDCADynCtrl.PclkDCAForceUpd;
		this.PclkDCAForceUpd = this.PclkDCADynCtrl.PclkDCAForceUpd;
      this.PclkDCAStaticCtrl0AC_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCAStaticCtrl0AC_p0::type_id::create("PclkDCAStaticCtrl0AC_p0",,get_full_name());
      if(this.PclkDCAStaticCtrl0AC_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkDCAStaticCtrl0AC_p0.cg_bits.option.name = {get_name(), ".", "PclkDCAStaticCtrl0AC_p0_bits"};
      this.PclkDCAStaticCtrl0AC_p0.configure(this, null, "");
      this.PclkDCAStaticCtrl0AC_p0.build();
      this.default_map.add_reg(this.PclkDCAStaticCtrl0AC_p0, `UVM_REG_ADDR_WIDTH'h803, "RW", 0);
		this.PclkDCAStaticCtrl0AC_p0_PclkDCACalModeAC = this.PclkDCAStaticCtrl0AC_p0.PclkDCACalModeAC;
		this.PclkDCACalModeAC = this.PclkDCAStaticCtrl0AC_p0.PclkDCACalModeAC;
		this.PclkDCAStaticCtrl0AC_p0_PclkDCAEnAC = this.PclkDCAStaticCtrl0AC_p0.PclkDCAEnAC;
		this.PclkDCAEnAC = this.PclkDCAStaticCtrl0AC_p0.PclkDCAEnAC;
		this.PclkDCAStaticCtrl0AC_p0_PclkDCATxLcdlPhSelAC = this.PclkDCAStaticCtrl0AC_p0.PclkDCATxLcdlPhSelAC;
		this.PclkDCATxLcdlPhSelAC = this.PclkDCAStaticCtrl0AC_p0.PclkDCATxLcdlPhSelAC;
		this.PclkDCAStaticCtrl0AC_p0_PclkDCDSettleAC = this.PclkDCAStaticCtrl0AC_p0.PclkDCDSettleAC;
		this.PclkDCDSettleAC = this.PclkDCAStaticCtrl0AC_p0.PclkDCDSettleAC;
		this.PclkDCAStaticCtrl0AC_p0_PclkDCDSampTimeAC = this.PclkDCAStaticCtrl0AC_p0.PclkDCDSampTimeAC;
		this.PclkDCDSampTimeAC = this.PclkDCAStaticCtrl0AC_p0.PclkDCDSampTimeAC;
      this.PclkDCASampCntAC = ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCASampCntAC::type_id::create("PclkDCASampCntAC",,get_full_name());
      if(this.PclkDCASampCntAC.has_coverage(UVM_CVR_ALL))
      	this.PclkDCASampCntAC.cg_bits.option.name = {get_name(), ".", "PclkDCASampCntAC_bits"};
      this.PclkDCASampCntAC.configure(this, null, "");
      this.PclkDCASampCntAC.build();
      this.default_map.add_reg(this.PclkDCASampCntAC, `UVM_REG_ADDR_WIDTH'h804, "RW", 0);
		this.PclkDCASampCntAC_PclkDCAQkSampCntAC = this.PclkDCASampCntAC.PclkDCAQkSampCntAC;
		this.PclkDCAQkSampCntAC = this.PclkDCASampCntAC.PclkDCAQkSampCntAC;
		this.PclkDCASampCntAC_PclkDCAFineSampCntAAC = this.PclkDCASampCntAC.PclkDCAFineSampCntAAC;
		this.PclkDCAFineSampCntAAC = this.PclkDCASampCntAC.PclkDCAFineSampCntAAC;
		this.PclkDCASampCntAC_PclkDCAFineSampCntBAC = this.PclkDCASampCntAC.PclkDCAFineSampCntBAC;
		this.PclkDCAFineSampCntBAC = this.PclkDCASampCntAC.PclkDCAFineSampCntBAC;
		this.PclkDCASampCntAC_PclkDCACoarseSampCntAC = this.PclkDCASampCntAC.PclkDCACoarseSampCntAC;
		this.PclkDCACoarseSampCntAC = this.PclkDCASampCntAC.PclkDCACoarseSampCntAC;
      this.PclkDCAHysMaskAC = ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCAHysMaskAC::type_id::create("PclkDCAHysMaskAC",,get_full_name());
      if(this.PclkDCAHysMaskAC.has_coverage(UVM_CVR_ALL))
      	this.PclkDCAHysMaskAC.cg_bits.option.name = {get_name(), ".", "PclkDCAHysMaskAC_bits"};
      this.PclkDCAHysMaskAC.configure(this, null, "");
      this.PclkDCAHysMaskAC.build();
      this.default_map.add_reg(this.PclkDCAHysMaskAC, `UVM_REG_ADDR_WIDTH'h805, "RW", 0);
		this.PclkDCAHysMaskAC_PclkDCAHysMaskAC = this.PclkDCAHysMaskAC.PclkDCAHysMaskAC;
      this.PclkDCACalFineBoundAC = ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCACalFineBoundAC::type_id::create("PclkDCACalFineBoundAC",,get_full_name());
      if(this.PclkDCACalFineBoundAC.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACalFineBoundAC.cg_bits.option.name = {get_name(), ".", "PclkDCACalFineBoundAC_bits"};
      this.PclkDCACalFineBoundAC.configure(this, null, "");
      this.PclkDCACalFineBoundAC.build();
      this.default_map.add_reg(this.PclkDCACalFineBoundAC, `UVM_REG_ADDR_WIDTH'h806, "RW", 0);
		this.PclkDCACalFineBoundAC_PclkDCAURMaxFineAC = this.PclkDCACalFineBoundAC.PclkDCAURMaxFineAC;
		this.PclkDCAURMaxFineAC = this.PclkDCACalFineBoundAC.PclkDCAURMaxFineAC;
		this.PclkDCACalFineBoundAC_PclkDCAURMinFineAC = this.PclkDCACalFineBoundAC.PclkDCAURMinFineAC;
		this.PclkDCAURMinFineAC = this.PclkDCACalFineBoundAC.PclkDCAURMinFineAC;
		this.PclkDCACalFineBoundAC_PclkDCALLMaxFineAC = this.PclkDCACalFineBoundAC.PclkDCALLMaxFineAC;
		this.PclkDCALLMaxFineAC = this.PclkDCACalFineBoundAC.PclkDCALLMaxFineAC;
		this.PclkDCACalFineBoundAC_PclkDCALLMinFineAC = this.PclkDCACalFineBoundAC.PclkDCALLMinFineAC;
		this.PclkDCALLMinFineAC = this.PclkDCACalFineBoundAC.PclkDCALLMinFineAC;
      this.PclkDCANextFineOnCoarseAC = ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCANextFineOnCoarseAC::type_id::create("PclkDCANextFineOnCoarseAC",,get_full_name());
      if(this.PclkDCANextFineOnCoarseAC.has_coverage(UVM_CVR_ALL))
      	this.PclkDCANextFineOnCoarseAC.cg_bits.option.name = {get_name(), ".", "PclkDCANextFineOnCoarseAC_bits"};
      this.PclkDCANextFineOnCoarseAC.configure(this, null, "");
      this.PclkDCANextFineOnCoarseAC.build();
      this.default_map.add_reg(this.PclkDCANextFineOnCoarseAC, `UVM_REG_ADDR_WIDTH'h807, "RW", 0);
		this.PclkDCANextFineOnCoarseAC_PclkDCACoarseIncFineURAC = this.PclkDCANextFineOnCoarseAC.PclkDCACoarseIncFineURAC;
		this.PclkDCACoarseIncFineURAC = this.PclkDCANextFineOnCoarseAC.PclkDCACoarseIncFineURAC;
		this.PclkDCANextFineOnCoarseAC_PclkDCACoarseDecFineURAC = this.PclkDCANextFineOnCoarseAC.PclkDCACoarseDecFineURAC;
		this.PclkDCACoarseDecFineURAC = this.PclkDCANextFineOnCoarseAC.PclkDCACoarseDecFineURAC;
		this.PclkDCANextFineOnCoarseAC_PclkDCACoarseIncFineLLAC = this.PclkDCANextFineOnCoarseAC.PclkDCACoarseIncFineLLAC;
		this.PclkDCACoarseIncFineLLAC = this.PclkDCANextFineOnCoarseAC.PclkDCACoarseIncFineLLAC;
		this.PclkDCANextFineOnCoarseAC_PclkDCACoarseDecFineLLAC = this.PclkDCANextFineOnCoarseAC.PclkDCACoarseDecFineLLAC;
		this.PclkDCACoarseDecFineLLAC = this.PclkDCANextFineOnCoarseAC.PclkDCACoarseDecFineLLAC;
      this.PclkDCAFullSearchIVACAC = ral_reg_DWC_DDRPHYA_AC1_p0_PclkDCAFullSearchIVACAC::type_id::create("PclkDCAFullSearchIVACAC",,get_full_name());
      if(this.PclkDCAFullSearchIVACAC.has_coverage(UVM_CVR_ALL))
      	this.PclkDCAFullSearchIVACAC.cg_bits.option.name = {get_name(), ".", "PclkDCAFullSearchIVACAC_bits"};
      this.PclkDCAFullSearchIVACAC.configure(this, null, "");
      this.PclkDCAFullSearchIVACAC.build();
      this.default_map.add_reg(this.PclkDCAFullSearchIVACAC, `UVM_REG_ADDR_WIDTH'h808, "RW", 0);
		this.PclkDCAFullSearchIVACAC_PclkDCAFineIVMaxAC = this.PclkDCAFullSearchIVACAC.PclkDCAFineIVMaxAC;
		this.PclkDCAFineIVMaxAC = this.PclkDCAFullSearchIVACAC.PclkDCAFineIVMaxAC;
		this.PclkDCAFullSearchIVACAC_PclkDCAFineIVMinAC = this.PclkDCAFullSearchIVACAC.PclkDCAFineIVMinAC;
		this.PclkDCAFineIVMinAC = this.PclkDCAFullSearchIVACAC.PclkDCAFineIVMinAC;
      this.LcdlTstCtrl = ral_reg_DWC_DDRPHYA_AC1_p0_LcdlTstCtrl::type_id::create("LcdlTstCtrl",,get_full_name());
      if(this.LcdlTstCtrl.has_coverage(UVM_CVR_ALL))
      	this.LcdlTstCtrl.cg_bits.option.name = {get_name(), ".", "LcdlTstCtrl_bits"};
      this.LcdlTstCtrl.configure(this, null, "");
      this.LcdlTstCtrl.build();
      this.default_map.add_reg(this.LcdlTstCtrl, `UVM_REG_ADDR_WIDTH'h884, "RW", 0);
		this.LcdlTstCtrl_LcdlTstCtrl = this.LcdlTstCtrl.LcdlTstCtrl;
      this.ACXTxDly_r8_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r8_p0::type_id::create("ACXTxDly_r8_p0",,get_full_name());
      if(this.ACXTxDly_r8_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly_r8_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDly_r8_p0_bits"};
      this.ACXTxDly_r8_p0.configure(this, null, "");
      this.ACXTxDly_r8_p0.build();
      this.default_map.add_reg(this.ACXTxDly_r8_p0, `UVM_REG_ADDR_WIDTH'h8D8, "RW", 0);
		this.ACXTxDly_r8_p0_ACXTxDly_r8_p0 = this.ACXTxDly_r8_p0.ACXTxDly_r8_p0;
      this.ACXTxDly2nMode_r8_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r8_p0::type_id::create("ACXTxDly2nMode_r8_p0",,get_full_name());
      if(this.ACXTxDly2nMode_r8_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly2nMode_r8_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDly2nMode_r8_p0_bits"};
      this.ACXTxDly2nMode_r8_p0.configure(this, null, "");
      this.ACXTxDly2nMode_r8_p0.build();
      this.default_map.add_reg(this.ACXTxDly2nMode_r8_p0, `UVM_REG_ADDR_WIDTH'h8DE, "RW", 0);
		this.ACXTxDly2nMode_r8_p0_ACXTxDly2nMode_r8_p0 = this.ACXTxDly2nMode_r8_p0.ACXTxDly2nMode_r8_p0;
      this.AcLoopBackEnLn0 = ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn0::type_id::create("AcLoopBackEnLn0",,get_full_name());
      if(this.AcLoopBackEnLn0.has_coverage(UVM_CVR_ALL))
      	this.AcLoopBackEnLn0.cg_bits.option.name = {get_name(), ".", "AcLoopBackEnLn0_bits"};
      this.AcLoopBackEnLn0.configure(this, null, "");
      this.AcLoopBackEnLn0.build();
      this.default_map.add_reg(this.AcLoopBackEnLn0, `UVM_REG_ADDR_WIDTH'h900, "RW", 0);
		this.AcLoopBackEnLn0_AcLoopBackEnLn0 = this.AcLoopBackEnLn0.AcLoopBackEnLn0;
      this.AcLoopBackEnLn1 = ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn1::type_id::create("AcLoopBackEnLn1",,get_full_name());
      if(this.AcLoopBackEnLn1.has_coverage(UVM_CVR_ALL))
      	this.AcLoopBackEnLn1.cg_bits.option.name = {get_name(), ".", "AcLoopBackEnLn1_bits"};
      this.AcLoopBackEnLn1.configure(this, null, "");
      this.AcLoopBackEnLn1.build();
      this.default_map.add_reg(this.AcLoopBackEnLn1, `UVM_REG_ADDR_WIDTH'h901, "RW", 0);
		this.AcLoopBackEnLn1_AcLoopBackEnLn1 = this.AcLoopBackEnLn1.AcLoopBackEnLn1;
      this.AcLoopBackEnLn2 = ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn2::type_id::create("AcLoopBackEnLn2",,get_full_name());
      if(this.AcLoopBackEnLn2.has_coverage(UVM_CVR_ALL))
      	this.AcLoopBackEnLn2.cg_bits.option.name = {get_name(), ".", "AcLoopBackEnLn2_bits"};
      this.AcLoopBackEnLn2.configure(this, null, "");
      this.AcLoopBackEnLn2.build();
      this.default_map.add_reg(this.AcLoopBackEnLn2, `UVM_REG_ADDR_WIDTH'h902, "RW", 0);
		this.AcLoopBackEnLn2_AcLoopBackEnLn2 = this.AcLoopBackEnLn2.AcLoopBackEnLn2;
      this.AcLoopBackEnLn3 = ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn3::type_id::create("AcLoopBackEnLn3",,get_full_name());
      if(this.AcLoopBackEnLn3.has_coverage(UVM_CVR_ALL))
      	this.AcLoopBackEnLn3.cg_bits.option.name = {get_name(), ".", "AcLoopBackEnLn3_bits"};
      this.AcLoopBackEnLn3.configure(this, null, "");
      this.AcLoopBackEnLn3.build();
      this.default_map.add_reg(this.AcLoopBackEnLn3, `UVM_REG_ADDR_WIDTH'h903, "RW", 0);
		this.AcLoopBackEnLn3_AcLoopBackEnLn3 = this.AcLoopBackEnLn3.AcLoopBackEnLn3;
      this.AcLoopBackEnLn4 = ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn4::type_id::create("AcLoopBackEnLn4",,get_full_name());
      if(this.AcLoopBackEnLn4.has_coverage(UVM_CVR_ALL))
      	this.AcLoopBackEnLn4.cg_bits.option.name = {get_name(), ".", "AcLoopBackEnLn4_bits"};
      this.AcLoopBackEnLn4.configure(this, null, "");
      this.AcLoopBackEnLn4.build();
      this.default_map.add_reg(this.AcLoopBackEnLn4, `UVM_REG_ADDR_WIDTH'h904, "RW", 0);
		this.AcLoopBackEnLn4_AcLoopBackEnLn4 = this.AcLoopBackEnLn4.AcLoopBackEnLn4;
      this.AcLoopBackEnLn5 = ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn5::type_id::create("AcLoopBackEnLn5",,get_full_name());
      if(this.AcLoopBackEnLn5.has_coverage(UVM_CVR_ALL))
      	this.AcLoopBackEnLn5.cg_bits.option.name = {get_name(), ".", "AcLoopBackEnLn5_bits"};
      this.AcLoopBackEnLn5.configure(this, null, "");
      this.AcLoopBackEnLn5.build();
      this.default_map.add_reg(this.AcLoopBackEnLn5, `UVM_REG_ADDR_WIDTH'h905, "RW", 0);
		this.AcLoopBackEnLn5_AcLoopBackEnLn5 = this.AcLoopBackEnLn5.AcLoopBackEnLn5;
      this.AcLoopBackEnLn6 = ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn6::type_id::create("AcLoopBackEnLn6",,get_full_name());
      if(this.AcLoopBackEnLn6.has_coverage(UVM_CVR_ALL))
      	this.AcLoopBackEnLn6.cg_bits.option.name = {get_name(), ".", "AcLoopBackEnLn6_bits"};
      this.AcLoopBackEnLn6.configure(this, null, "");
      this.AcLoopBackEnLn6.build();
      this.default_map.add_reg(this.AcLoopBackEnLn6, `UVM_REG_ADDR_WIDTH'h906, "RW", 0);
		this.AcLoopBackEnLn6_AcLoopBackEnLn6 = this.AcLoopBackEnLn6.AcLoopBackEnLn6;
      this.AcLoopBackEnLn7 = ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn7::type_id::create("AcLoopBackEnLn7",,get_full_name());
      if(this.AcLoopBackEnLn7.has_coverage(UVM_CVR_ALL))
      	this.AcLoopBackEnLn7.cg_bits.option.name = {get_name(), ".", "AcLoopBackEnLn7_bits"};
      this.AcLoopBackEnLn7.configure(this, null, "");
      this.AcLoopBackEnLn7.build();
      this.default_map.add_reg(this.AcLoopBackEnLn7, `UVM_REG_ADDR_WIDTH'h907, "RW", 0);
		this.AcLoopBackEnLn7_AcLoopBackEnLn7 = this.AcLoopBackEnLn7.AcLoopBackEnLn7;
      this.AcLoopBackEnLn8 = ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn8::type_id::create("AcLoopBackEnLn8",,get_full_name());
      if(this.AcLoopBackEnLn8.has_coverage(UVM_CVR_ALL))
      	this.AcLoopBackEnLn8.cg_bits.option.name = {get_name(), ".", "AcLoopBackEnLn8_bits"};
      this.AcLoopBackEnLn8.configure(this, null, "");
      this.AcLoopBackEnLn8.build();
      this.default_map.add_reg(this.AcLoopBackEnLn8, `UVM_REG_ADDR_WIDTH'h908, "RW", 0);
		this.AcLoopBackEnLn8_AcLoopBackEnLn8 = this.AcLoopBackEnLn8.AcLoopBackEnLn8;
      this.AcLoopBackEnLn9 = ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn9::type_id::create("AcLoopBackEnLn9",,get_full_name());
      if(this.AcLoopBackEnLn9.has_coverage(UVM_CVR_ALL))
      	this.AcLoopBackEnLn9.cg_bits.option.name = {get_name(), ".", "AcLoopBackEnLn9_bits"};
      this.AcLoopBackEnLn9.configure(this, null, "");
      this.AcLoopBackEnLn9.build();
      this.default_map.add_reg(this.AcLoopBackEnLn9, `UVM_REG_ADDR_WIDTH'h909, "RW", 0);
		this.AcLoopBackEnLn9_AcLoopBackEnLn9 = this.AcLoopBackEnLn9.AcLoopBackEnLn9;
      this.AcLoopBackEnLn10 = ral_reg_DWC_DDRPHYA_AC1_p0_AcLoopBackEnLn10::type_id::create("AcLoopBackEnLn10",,get_full_name());
      if(this.AcLoopBackEnLn10.has_coverage(UVM_CVR_ALL))
      	this.AcLoopBackEnLn10.cg_bits.option.name = {get_name(), ".", "AcLoopBackEnLn10_bits"};
      this.AcLoopBackEnLn10.configure(this, null, "");
      this.AcLoopBackEnLn10.build();
      this.default_map.add_reg(this.AcLoopBackEnLn10, `UVM_REG_ADDR_WIDTH'h90A, "RW", 0);
		this.AcLoopBackEnLn10_AcLoopBackEnLn10 = this.AcLoopBackEnLn10.AcLoopBackEnLn10;
      this.ACXTxDly_r9_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly_r9_p0::type_id::create("ACXTxDly_r9_p0",,get_full_name());
      if(this.ACXTxDly_r9_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly_r9_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDly_r9_p0_bits"};
      this.ACXTxDly_r9_p0.configure(this, null, "");
      this.ACXTxDly_r9_p0.build();
      this.default_map.add_reg(this.ACXTxDly_r9_p0, `UVM_REG_ADDR_WIDTH'h9D8, "RW", 0);
		this.ACXTxDly_r9_p0_ACXTxDly_r9_p0 = this.ACXTxDly_r9_p0.ACXTxDly_r9_p0;
      this.ACXTxDly2nMode_r9_p0 = ral_reg_DWC_DDRPHYA_AC1_p0_ACXTxDly2nMode_r9_p0::type_id::create("ACXTxDly2nMode_r9_p0",,get_full_name());
      if(this.ACXTxDly2nMode_r9_p0.has_coverage(UVM_CVR_ALL))
      	this.ACXTxDly2nMode_r9_p0.cg_bits.option.name = {get_name(), ".", "ACXTxDly2nMode_r9_p0_bits"};
      this.ACXTxDly2nMode_r9_p0.configure(this, null, "");
      this.ACXTxDly2nMode_r9_p0.build();
      this.default_map.add_reg(this.ACXTxDly2nMode_r9_p0, `UVM_REG_ADDR_WIDTH'h9DE, "RW", 0);
		this.ACXTxDly2nMode_r9_p0_ACXTxDly2nMode_r9_p0 = this.ACXTxDly2nMode_r9_p0.ACXTxDly2nMode_r9_p0;
      this.ATestPrbsErrCntSE0 = ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE0::type_id::create("ATestPrbsErrCntSE0",,get_full_name());
      if(this.ATestPrbsErrCntSE0.has_coverage(UVM_CVR_ALL))
      	this.ATestPrbsErrCntSE0.cg_bits.option.name = {get_name(), ".", "ATestPrbsErrCntSE0_bits"};
      this.ATestPrbsErrCntSE0.configure(this, null, "");
      this.ATestPrbsErrCntSE0.build();
      this.default_map.add_reg(this.ATestPrbsErrCntSE0, `UVM_REG_ADDR_WIDTH'hB00, "RO", 0);
		this.ATestPrbsErrCntSE0_ATestPrbsErrCntSE0 = this.ATestPrbsErrCntSE0.ATestPrbsErrCntSE0;
      this.ATestPrbsErrCntSE1 = ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE1::type_id::create("ATestPrbsErrCntSE1",,get_full_name());
      if(this.ATestPrbsErrCntSE1.has_coverage(UVM_CVR_ALL))
      	this.ATestPrbsErrCntSE1.cg_bits.option.name = {get_name(), ".", "ATestPrbsErrCntSE1_bits"};
      this.ATestPrbsErrCntSE1.configure(this, null, "");
      this.ATestPrbsErrCntSE1.build();
      this.default_map.add_reg(this.ATestPrbsErrCntSE1, `UVM_REG_ADDR_WIDTH'hB01, "RO", 0);
		this.ATestPrbsErrCntSE1_ATestPrbsErrCntSE1 = this.ATestPrbsErrCntSE1.ATestPrbsErrCntSE1;
      this.ATestPrbsErrCntSE2 = ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE2::type_id::create("ATestPrbsErrCntSE2",,get_full_name());
      if(this.ATestPrbsErrCntSE2.has_coverage(UVM_CVR_ALL))
      	this.ATestPrbsErrCntSE2.cg_bits.option.name = {get_name(), ".", "ATestPrbsErrCntSE2_bits"};
      this.ATestPrbsErrCntSE2.configure(this, null, "");
      this.ATestPrbsErrCntSE2.build();
      this.default_map.add_reg(this.ATestPrbsErrCntSE2, `UVM_REG_ADDR_WIDTH'hB02, "RO", 0);
		this.ATestPrbsErrCntSE2_ATestPrbsErrCntSE2 = this.ATestPrbsErrCntSE2.ATestPrbsErrCntSE2;
      this.ATestPrbsErrCntSE3 = ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE3::type_id::create("ATestPrbsErrCntSE3",,get_full_name());
      if(this.ATestPrbsErrCntSE3.has_coverage(UVM_CVR_ALL))
      	this.ATestPrbsErrCntSE3.cg_bits.option.name = {get_name(), ".", "ATestPrbsErrCntSE3_bits"};
      this.ATestPrbsErrCntSE3.configure(this, null, "");
      this.ATestPrbsErrCntSE3.build();
      this.default_map.add_reg(this.ATestPrbsErrCntSE3, `UVM_REG_ADDR_WIDTH'hB03, "RO", 0);
		this.ATestPrbsErrCntSE3_ATestPrbsErrCntSE3 = this.ATestPrbsErrCntSE3.ATestPrbsErrCntSE3;
      this.ATestPrbsErrCntSE4 = ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE4::type_id::create("ATestPrbsErrCntSE4",,get_full_name());
      if(this.ATestPrbsErrCntSE4.has_coverage(UVM_CVR_ALL))
      	this.ATestPrbsErrCntSE4.cg_bits.option.name = {get_name(), ".", "ATestPrbsErrCntSE4_bits"};
      this.ATestPrbsErrCntSE4.configure(this, null, "");
      this.ATestPrbsErrCntSE4.build();
      this.default_map.add_reg(this.ATestPrbsErrCntSE4, `UVM_REG_ADDR_WIDTH'hB04, "RO", 0);
		this.ATestPrbsErrCntSE4_ATestPrbsErrCntSE4 = this.ATestPrbsErrCntSE4.ATestPrbsErrCntSE4;
      this.ATestPrbsErrCntSE5 = ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE5::type_id::create("ATestPrbsErrCntSE5",,get_full_name());
      if(this.ATestPrbsErrCntSE5.has_coverage(UVM_CVR_ALL))
      	this.ATestPrbsErrCntSE5.cg_bits.option.name = {get_name(), ".", "ATestPrbsErrCntSE5_bits"};
      this.ATestPrbsErrCntSE5.configure(this, null, "");
      this.ATestPrbsErrCntSE5.build();
      this.default_map.add_reg(this.ATestPrbsErrCntSE5, `UVM_REG_ADDR_WIDTH'hB05, "RO", 0);
		this.ATestPrbsErrCntSE5_ATestPrbsErrCntSE5 = this.ATestPrbsErrCntSE5.ATestPrbsErrCntSE5;
      this.ATestPrbsErrCntSE6 = ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE6::type_id::create("ATestPrbsErrCntSE6",,get_full_name());
      if(this.ATestPrbsErrCntSE6.has_coverage(UVM_CVR_ALL))
      	this.ATestPrbsErrCntSE6.cg_bits.option.name = {get_name(), ".", "ATestPrbsErrCntSE6_bits"};
      this.ATestPrbsErrCntSE6.configure(this, null, "");
      this.ATestPrbsErrCntSE6.build();
      this.default_map.add_reg(this.ATestPrbsErrCntSE6, `UVM_REG_ADDR_WIDTH'hB06, "RO", 0);
		this.ATestPrbsErrCntSE6_ATestPrbsErrCntSE6 = this.ATestPrbsErrCntSE6.ATestPrbsErrCntSE6;
      this.ATestPrbsErrCntSE7 = ral_reg_DWC_DDRPHYA_AC1_p0_ATestPrbsErrCntSE7::type_id::create("ATestPrbsErrCntSE7",,get_full_name());
      if(this.ATestPrbsErrCntSE7.has_coverage(UVM_CVR_ALL))
      	this.ATestPrbsErrCntSE7.cg_bits.option.name = {get_name(), ".", "ATestPrbsErrCntSE7_bits"};
      this.ATestPrbsErrCntSE7.configure(this, null, "");
      this.ATestPrbsErrCntSE7.build();
      this.default_map.add_reg(this.ATestPrbsErrCntSE7, `UVM_REG_ADDR_WIDTH'hB07, "RO", 0);
		this.ATestPrbsErrCntSE7_ATestPrbsErrCntSE7 = this.ATestPrbsErrCntSE7.ATestPrbsErrCntSE7;
   endfunction : build

	`uvm_object_utils(ral_block_DWC_DDRPHYA_AC1_p0)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_DDRPHYA_AC1_p0


endpackage
`endif
