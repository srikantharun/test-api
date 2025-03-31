`ifndef RAL_DWC_DDRPHYA_HMMAS0_P0_PKG
`define RAL_DWC_DDRPHYA_HMMAS0_P0_PKG

package ral_DWC_DDRPHYA_HMMAS0_p0_pkg;
import uvm_pkg::*;

class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllPwrDn extends uvm_reg;
	rand uvm_reg_field CPllPwrDn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllPwrDn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllPwrDn");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllPwrDn = uvm_reg_field::type_id::create("CPllPwrDn",,get_full_name());
      this.CPllPwrDn.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllPwrDn)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllPwrDn


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllStandby extends uvm_reg;
	rand uvm_reg_field CPllStandby;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllStandby: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllStandby");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllStandby = uvm_reg_field::type_id::create("CPllStandby",,get_full_name());
      this.CPllStandby.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllStandby)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllStandby


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllBypassMode extends uvm_reg;
	rand uvm_reg_field CPllBypassMode;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllBypassMode: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllBypassMode");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllBypassMode = uvm_reg_field::type_id::create("CPllBypassMode",,get_full_name());
      this.CPllBypassMode.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllBypassMode)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllBypassMode


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllStartLock extends uvm_reg;
	rand uvm_reg_field CPllPreset;
	rand uvm_reg_field CPllGearShift;
	rand uvm_reg_field CPllFastRelock;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllPreset: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CPllGearShift: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CPllFastRelock: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllStartLock");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllPreset = uvm_reg_field::type_id::create("CPllPreset",,get_full_name());
      this.CPllPreset.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.CPllGearShift = uvm_reg_field::type_id::create("CPllGearShift",,get_full_name());
      this.CPllGearShift.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.CPllFastRelock = uvm_reg_field::type_id::create("CPllFastRelock",,get_full_name());
      this.CPllFastRelock.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllStartLock)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllStartLock


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl0 extends uvm_reg;
	rand uvm_reg_field CPllLockCntSel;
	rand uvm_reg_field CReservedPllLockCntSel;
	rand uvm_reg_field CPllLockPhSel;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllLockCntSel: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CReservedPllLockCntSel: coverpoint {m_data[3:1], m_is_read} iff(m_be) {
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
	   CPllLockPhSel: coverpoint {m_data[5:4], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllCtrl0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllLockCntSel = uvm_reg_field::type_id::create("CPllLockCntSel",,get_full_name());
      this.CPllLockCntSel.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.CReservedPllLockCntSel = uvm_reg_field::type_id::create("CReservedPllLockCntSel",,get_full_name());
      this.CReservedPllLockCntSel.configure(this, 3, 1, "RW", 0, 3'h0, 1, 0, 0);
      this.CPllLockPhSel = uvm_reg_field::type_id::create("CPllLockPhSel",,get_full_name());
      this.CPllLockPhSel.configure(this, 2, 4, "RW", 0, 2'h1, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl0


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl1_p0 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllCtrl1_p0");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl1_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl1_p0


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl3 extends uvm_reg;
	rand uvm_reg_field CReservedPllCtrl3;
	rand uvm_reg_field CPllMaxRange;
	rand uvm_reg_field CPllForceCal;
	rand uvm_reg_field CPllEnCal;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CReservedPllCtrl3: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   CPllMaxRange: coverpoint {m_data[8:4], m_is_read} iff(m_be) {
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
	   CPllForceCal: coverpoint {m_data[9:9], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CPllEnCal: coverpoint {m_data[10:10], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllCtrl3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CReservedPllCtrl3 = uvm_reg_field::type_id::create("CReservedPllCtrl3",,get_full_name());
      this.CReservedPllCtrl3.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.CPllMaxRange = uvm_reg_field::type_id::create("CPllMaxRange",,get_full_name());
      this.CPllMaxRange.configure(this, 5, 4, "RW", 0, 5'h1f, 1, 0, 0);
      this.CPllForceCal = uvm_reg_field::type_id::create("CPllForceCal",,get_full_name());
      this.CPllForceCal.configure(this, 1, 9, "RW", 0, 1'h0, 1, 0, 0);
      this.CPllEnCal = uvm_reg_field::type_id::create("CPllEnCal",,get_full_name());
      this.CPllEnCal.configure(this, 1, 10, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl3


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl4_p0 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllCtrl4_p0");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl4_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl4_p0


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl5_p0 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllCtrl5_p0");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl5_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl5_p0


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllDacValIn_p0 extends uvm_reg;
	rand uvm_reg_field CPllDacValIn_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllDacValIn_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllDacValIn_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllDacValIn_p0 = uvm_reg_field::type_id::create("CPllDacValIn_p0",,get_full_name());
      this.CPllDacValIn_p0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllDacValIn_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllDacValIn_p0


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CMasterReserved_p0 extends uvm_reg;
	rand uvm_reg_field CMasterReserved_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CMasterReserved_p0: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CMasterReserved_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CMasterReserved_p0 = uvm_reg_field::type_id::create("CMasterReserved_p0",,get_full_name());
      this.CMasterReserved_p0.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CMasterReserved_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CMasterReserved_p0


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllTst extends uvm_reg;
	rand uvm_reg_field CPllAnaTstEn;
	rand uvm_reg_field CPllAnaTstSel;
	rand uvm_reg_field CPllDigTstSel;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllAnaTstEn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CPllAnaTstSel: coverpoint {m_data[6:1], m_is_read} iff(m_be) {
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
	   CPllDigTstSel: coverpoint {m_data[12:7], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllTst");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllAnaTstEn = uvm_reg_field::type_id::create("CPllAnaTstEn",,get_full_name());
      this.CPllAnaTstEn.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.CPllAnaTstSel = uvm_reg_field::type_id::create("CPllAnaTstSel",,get_full_name());
      this.CPllAnaTstSel.configure(this, 6, 1, "RW", 0, 6'h0, 1, 0, 0);
      this.CPllDigTstSel = uvm_reg_field::type_id::create("CPllDigTstSel",,get_full_name());
      this.CPllDigTstSel.configure(this, 6, 7, "RW", 0, 6'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllTst)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllTst


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockStatus extends uvm_reg;
	uvm_reg_field CPllLockStatus;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllLockStatus: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllLockStatus");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllLockStatus = uvm_reg_field::type_id::create("CPllLockStatus",,get_full_name());
      this.CPllLockStatus.configure(this, 1, 0, "RO", 1, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockStatus)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockStatus


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg0 extends uvm_reg;
	rand uvm_reg_field CPllUPllProg0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllUPllProg0: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllUPllProg0 = uvm_reg_field::type_id::create("CPllUPllProg0",,get_full_name());
      this.CPllUPllProg0.configure(this, 16, 0, "RW", 0, 16'h124, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg0


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg1 extends uvm_reg;
	rand uvm_reg_field CPllUPllProg1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllUPllProg1: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg1");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllUPllProg1 = uvm_reg_field::type_id::create("CPllUPllProg1",,get_full_name());
      this.CPllUPllProg1.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg1


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg2 extends uvm_reg;
	rand uvm_reg_field CPllUPllProg2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllUPllProg2: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllUPllProg2 = uvm_reg_field::type_id::create("CPllUPllProg2",,get_full_name());
      this.CPllUPllProg2.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg2


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg3 extends uvm_reg;
	rand uvm_reg_field CPllUPllProg3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllUPllProg3: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg3");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllUPllProg3 = uvm_reg_field::type_id::create("CPllUPllProg3",,get_full_name());
      this.CPllUPllProg3.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg3


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllEndofCal extends uvm_reg;
	uvm_reg_field CPllEndofCal;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllEndofCal: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllEndofCal");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllEndofCal = uvm_reg_field::type_id::create("CPllEndofCal",,get_full_name());
      this.CPllEndofCal.configure(this, 1, 0, "RO", 1, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllEndofCal)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllEndofCal


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllStandbyEff extends uvm_reg;
	uvm_reg_field CPllStandbyEff;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllStandbyEff: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllStandbyEff");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllStandbyEff = uvm_reg_field::type_id::create("CPllStandbyEff",,get_full_name());
      this.CPllStandbyEff.configure(this, 1, 0, "RO", 1, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllStandbyEff)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllStandbyEff


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllDacValOut extends uvm_reg;
	uvm_reg_field CPllDacValOut;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllDacValOut: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {6'b????00};
	      wildcard bins bit_0_wr_as_1 = {6'b????10};
	      wildcard bins bit_0_rd = {6'b?????1};
	      wildcard bins bit_1_wr_as_0 = {6'b???0?0};
	      wildcard bins bit_1_wr_as_1 = {6'b???1?0};
	      wildcard bins bit_1_rd = {6'b?????1};
	      wildcard bins bit_2_wr_as_0 = {6'b??0??0};
	      wildcard bins bit_2_wr_as_1 = {6'b??1??0};
	      wildcard bins bit_2_rd = {6'b?????1};
	      wildcard bins bit_3_wr_as_0 = {6'b?0???0};
	      wildcard bins bit_3_wr_as_1 = {6'b?1???0};
	      wildcard bins bit_3_rd = {6'b?????1};
	      wildcard bins bit_4_wr_as_0 = {6'b0????0};
	      wildcard bins bit_4_wr_as_1 = {6'b1????0};
	      wildcard bins bit_4_rd = {6'b?????1};
	      option.weight = 15;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllDacValOut");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllDacValOut = uvm_reg_field::type_id::create("CPllDacValOut",,get_full_name());
      this.CPllDacValOut.configure(this, 5, 0, "RO", 1, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllDacValOut)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllDacValOut


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockedStatus extends uvm_reg;
	uvm_reg_field CPllLocked;
	uvm_reg_field CPllUnlocked;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllLocked: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   CPllUnlocked: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllLockedStatus");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllLocked = uvm_reg_field::type_id::create("CPllLocked",,get_full_name());
      this.CPllLocked.configure(this, 1, 0, "RO", 1, 1'h0, 1, 0, 0);
      this.CPllUnlocked = uvm_reg_field::type_id::create("CPllUnlocked",,get_full_name());
      this.CPllUnlocked.configure(this, 1, 1, "RO", 1, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockedStatus)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockedStatus


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockedControl extends uvm_reg;
	rand uvm_reg_field CPllLockedClear;
	rand uvm_reg_field CPllLockedHiCtrMode;
	rand uvm_reg_field CPllLockedTransCtrMode;
	rand uvm_reg_field CPllLockedCtrsEnable;
	rand uvm_reg_field CPllLockedCtrsClear;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllLockedClear: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CPllLockedHiCtrMode: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CPllLockedTransCtrMode: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CPllLockedCtrsEnable: coverpoint {m_data[3:3], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   CPllLockedCtrsClear: coverpoint {m_data[4:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllLockedControl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllLockedClear = uvm_reg_field::type_id::create("CPllLockedClear",,get_full_name());
      this.CPllLockedClear.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.CPllLockedHiCtrMode = uvm_reg_field::type_id::create("CPllLockedHiCtrMode",,get_full_name());
      this.CPllLockedHiCtrMode.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.CPllLockedTransCtrMode = uvm_reg_field::type_id::create("CPllLockedTransCtrMode",,get_full_name());
      this.CPllLockedTransCtrMode.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
      this.CPllLockedCtrsEnable = uvm_reg_field::type_id::create("CPllLockedCtrsEnable",,get_full_name());
      this.CPllLockedCtrsEnable.configure(this, 1, 3, "RW", 0, 1'h0, 1, 0, 0);
      this.CPllLockedCtrsClear = uvm_reg_field::type_id::create("CPllLockedCtrsClear",,get_full_name());
      this.CPllLockedCtrsClear.configure(this, 1, 4, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockedControl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockedControl


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockedHiCtr extends uvm_reg;
	uvm_reg_field CPllLockedHiCtr;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllLockedHiCtr: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllLockedHiCtr");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllLockedHiCtr = uvm_reg_field::type_id::create("CPllLockedHiCtr",,get_full_name());
      this.CPllLockedHiCtr.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockedHiCtr)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockedHiCtr


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockedTransCtr extends uvm_reg;
	uvm_reg_field CPllLockedTransCtr;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPllLockedTransCtr: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_CPllLockedTransCtr");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPllLockedTransCtr = uvm_reg_field::type_id::create("CPllLockedTransCtr",,get_full_name());
      this.CPllLockedTransCtr.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockedTransCtr)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockedTransCtr


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_MtestMuxSelMAS extends uvm_reg;
	rand uvm_reg_field MtestMuxSelMAS;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   MtestMuxSelMAS: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_MtestMuxSelMAS");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MtestMuxSelMAS = uvm_reg_field::type_id::create("MtestMuxSelMAS",,get_full_name());
      this.MtestMuxSelMAS.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_MtestMuxSelMAS)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_MtestMuxSelMAS


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_HMPclkPtrInitVal_p0 extends uvm_reg;
	rand uvm_reg_field HMPclkPtrInitVal_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HMPclkPtrInitVal_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_HMPclkPtrInitVal_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMPclkPtrInitVal_p0 = uvm_reg_field::type_id::create("HMPclkPtrInitVal_p0",,get_full_name());
      this.HMPclkPtrInitVal_p0.configure(this, 5, 0, "RW", 0, 5'h2, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_HMPclkPtrInitVal_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_HMPclkPtrInitVal_p0


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_HMMASParityInvert extends uvm_reg;
	rand uvm_reg_field HMMASParityInvert;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HMMASParityInvert: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_HMMASParityInvert");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMMASParityInvert = uvm_reg_field::type_id::create("HMMASParityInvert",,get_full_name());
      this.HMMASParityInvert.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_HMMASParityInvert)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_HMMASParityInvert


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_ScratchPadHMMAS extends uvm_reg;
	rand uvm_reg_field ScratchPadHMMAS;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ScratchPadHMMAS: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_ScratchPadHMMAS");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ScratchPadHMMAS = uvm_reg_field::type_id::create("ScratchPadHMMAS",,get_full_name());
      this.ScratchPadHMMAS.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_ScratchPadHMMAS)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_ScratchPadHMMAS


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_HMReserved0 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_HMReserved0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMReserved0 = uvm_reg_field::type_id::create("HMReserved0",,get_full_name());
      this.HMReserved0.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_HMReserved0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_HMReserved0


class ral_reg_DWC_DDRPHYA_HMMAS0_p0_HMReservedP1_p0 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0_HMReservedP1_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMReservedP1_p0 = uvm_reg_field::type_id::create("HMReservedP1_p0",,get_full_name());
      this.HMReservedP1_p0.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMMAS0_p0_HMReservedP1_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMMAS0_p0_HMReservedP1_p0


class ral_block_DWC_DDRPHYA_HMMAS0_p0 extends uvm_reg_block;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllPwrDn CPllPwrDn;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllStandby CPllStandby;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllBypassMode CPllBypassMode;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllStartLock CPllStartLock;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl0 CPllCtrl0;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl1_p0 CPllCtrl1_p0;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl3 CPllCtrl3;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl4_p0 CPllCtrl4_p0;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl5_p0 CPllCtrl5_p0;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllDacValIn_p0 CPllDacValIn_p0;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CMasterReserved_p0 CMasterReserved_p0;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllTst CPllTst;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockStatus CPllLockStatus;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg0 CPllUPllProg0;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg1 CPllUPllProg1;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg2 CPllUPllProg2;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg3 CPllUPllProg3;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllEndofCal CPllEndofCal;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllStandbyEff CPllStandbyEff;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllDacValOut CPllDacValOut;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockedStatus CPllLockedStatus;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockedControl CPllLockedControl;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockedHiCtr CPllLockedHiCtr;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockedTransCtr CPllLockedTransCtr;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_MtestMuxSelMAS MtestMuxSelMAS;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_HMPclkPtrInitVal_p0 HMPclkPtrInitVal_p0;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_HMMASParityInvert HMMASParityInvert;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_ScratchPadHMMAS ScratchPadHMMAS;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_HMReserved0 HMReserved0;
	rand ral_reg_DWC_DDRPHYA_HMMAS0_p0_HMReservedP1_p0 HMReservedP1_p0;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field CPllPwrDn_CPllPwrDn;
	rand uvm_reg_field CPllStandby_CPllStandby;
	rand uvm_reg_field CPllBypassMode_CPllBypassMode;
	rand uvm_reg_field CPllStartLock_CPllPreset;
	rand uvm_reg_field CPllPreset;
	rand uvm_reg_field CPllStartLock_CPllGearShift;
	rand uvm_reg_field CPllGearShift;
	rand uvm_reg_field CPllStartLock_CPllFastRelock;
	rand uvm_reg_field CPllFastRelock;
	rand uvm_reg_field CPllCtrl0_CPllLockCntSel;
	rand uvm_reg_field CPllLockCntSel;
	rand uvm_reg_field CPllCtrl0_CReservedPllLockCntSel;
	rand uvm_reg_field CReservedPllLockCntSel;
	rand uvm_reg_field CPllCtrl0_CPllLockPhSel;
	rand uvm_reg_field CPllLockPhSel;
	rand uvm_reg_field CPllCtrl1_p0_CPllCpIntCtrl;
	rand uvm_reg_field CPllCpIntCtrl;
	rand uvm_reg_field CPllCtrl1_p0_CReservedPllCpIntCtrl;
	rand uvm_reg_field CReservedPllCpIntCtrl;
	rand uvm_reg_field CPllCtrl1_p0_CPllCpPropCtrl;
	rand uvm_reg_field CPllCpPropCtrl;
	rand uvm_reg_field CPllCtrl3_CReservedPllCtrl3;
	rand uvm_reg_field CReservedPllCtrl3;
	rand uvm_reg_field CPllCtrl3_CPllMaxRange;
	rand uvm_reg_field CPllMaxRange;
	rand uvm_reg_field CPllCtrl3_CPllForceCal;
	rand uvm_reg_field CPllForceCal;
	rand uvm_reg_field CPllCtrl3_CPllEnCal;
	rand uvm_reg_field CPllEnCal;
	rand uvm_reg_field CPllCtrl4_p0_CPllCpIntGsCtrl;
	rand uvm_reg_field CPllCpIntGsCtrl;
	rand uvm_reg_field CPllCtrl4_p0_CReservedPllCpIntGsCtrl;
	rand uvm_reg_field CReservedPllCpIntGsCtrl;
	rand uvm_reg_field CPllCtrl4_p0_CPllCpPropGsCtrl;
	rand uvm_reg_field CPllCpPropGsCtrl;
	rand uvm_reg_field CPllCtrl5_p0_CPllDivSel;
	rand uvm_reg_field CPllDivSel;
	rand uvm_reg_field CPllCtrl5_p0_CPllV2IMode;
	rand uvm_reg_field CPllV2IMode;
	rand uvm_reg_field CPllCtrl5_p0_CPllVcoLowFreq;
	rand uvm_reg_field CPllVcoLowFreq;
	rand uvm_reg_field CPllDacValIn_p0_CPllDacValIn_p0;
	rand uvm_reg_field CMasterReserved_p0_CMasterReserved_p0;
	rand uvm_reg_field CPllTst_CPllAnaTstEn;
	rand uvm_reg_field CPllAnaTstEn;
	rand uvm_reg_field CPllTst_CPllAnaTstSel;
	rand uvm_reg_field CPllAnaTstSel;
	rand uvm_reg_field CPllTst_CPllDigTstSel;
	rand uvm_reg_field CPllDigTstSel;
	uvm_reg_field CPllLockStatus_CPllLockStatus;
	rand uvm_reg_field CPllUPllProg0_CPllUPllProg0;
	rand uvm_reg_field CPllUPllProg1_CPllUPllProg1;
	rand uvm_reg_field CPllUPllProg2_CPllUPllProg2;
	rand uvm_reg_field CPllUPllProg3_CPllUPllProg3;
	uvm_reg_field CPllEndofCal_CPllEndofCal;
	uvm_reg_field CPllStandbyEff_CPllStandbyEff;
	uvm_reg_field CPllDacValOut_CPllDacValOut;
	uvm_reg_field CPllLockedStatus_CPllLocked;
	uvm_reg_field CPllLocked;
	uvm_reg_field CPllLockedStatus_CPllUnlocked;
	uvm_reg_field CPllUnlocked;
	rand uvm_reg_field CPllLockedControl_CPllLockedClear;
	rand uvm_reg_field CPllLockedClear;
	rand uvm_reg_field CPllLockedControl_CPllLockedHiCtrMode;
	rand uvm_reg_field CPllLockedHiCtrMode;
	rand uvm_reg_field CPllLockedControl_CPllLockedTransCtrMode;
	rand uvm_reg_field CPllLockedTransCtrMode;
	rand uvm_reg_field CPllLockedControl_CPllLockedCtrsEnable;
	rand uvm_reg_field CPllLockedCtrsEnable;
	rand uvm_reg_field CPllLockedControl_CPllLockedCtrsClear;
	rand uvm_reg_field CPllLockedCtrsClear;
	uvm_reg_field CPllLockedHiCtr_CPllLockedHiCtr;
	uvm_reg_field CPllLockedTransCtr_CPllLockedTransCtr;
	rand uvm_reg_field MtestMuxSelMAS_MtestMuxSelMAS;
	rand uvm_reg_field HMPclkPtrInitVal_p0_HMPclkPtrInitVal_p0;
	rand uvm_reg_field HMMASParityInvert_HMMASParityInvert;
	rand uvm_reg_field ScratchPadHMMAS_ScratchPadHMMAS;
	rand uvm_reg_field HMReserved0_HMReserved0;
	rand uvm_reg_field HMReservedP1_p0_HMReservedP1_p0;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	CPllPwrDn : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h0 };
		option.weight = 1;
	}

	CPllStandby : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1 };
		option.weight = 1;
	}

	CPllBypassMode : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2 };
		option.weight = 1;
	}

	CPllStartLock : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3 };
		option.weight = 1;
	}

	CPllCtrl0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4 };
		option.weight = 1;
	}

	CPllCtrl1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5 };
		option.weight = 1;
	}

	CPllCtrl3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h6 };
		option.weight = 1;
	}

	CPllCtrl4_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h7 };
		option.weight = 1;
	}

	CPllCtrl5_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h8 };
		option.weight = 1;
	}

	CPllDacValIn_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h9 };
		option.weight = 1;
	}

	CMasterReserved_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA };
		option.weight = 1;
	}

	CPllTst : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB };
		option.weight = 1;
	}

	CPllLockStatus : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC };
		option.weight = 1;
	}

	CPllUPllProg0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD };
		option.weight = 1;
	}

	CPllUPllProg1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hE };
		option.weight = 1;
	}

	CPllUPllProg2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF };
		option.weight = 1;
	}

	CPllUPllProg3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h10 };
		option.weight = 1;
	}

	CPllEndofCal : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h11 };
		option.weight = 1;
	}

	CPllStandbyEff : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h12 };
		option.weight = 1;
	}

	CPllDacValOut : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h13 };
		option.weight = 1;
	}

	CPllLockedStatus : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h14 };
		option.weight = 1;
	}

	CPllLockedControl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h15 };
		option.weight = 1;
	}

	CPllLockedHiCtr : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h16 };
		option.weight = 1;
	}

	CPllLockedTransCtr : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h17 };
		option.weight = 1;
	}

	MtestMuxSelMAS : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1A };
		option.weight = 1;
	}

	HMPclkPtrInitVal_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h40 };
		option.weight = 1;
	}

	HMMASParityInvert : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4D };
		option.weight = 1;
	}

	ScratchPadHMMAS : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h7D };
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
endgroup
	function new(string name = "DWC_DDRPHYA_HMMAS0_p0");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.CPllPwrDn = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllPwrDn::type_id::create("CPllPwrDn",,get_full_name());
      if(this.CPllPwrDn.has_coverage(UVM_CVR_ALL))
      	this.CPllPwrDn.cg_bits.option.name = {get_name(), ".", "CPllPwrDn_bits"};
      this.CPllPwrDn.configure(this, null, "");
      this.CPllPwrDn.build();
      this.default_map.add_reg(this.CPllPwrDn, `UVM_REG_ADDR_WIDTH'h0, "RW", 0);
		this.CPllPwrDn_CPllPwrDn = this.CPllPwrDn.CPllPwrDn;
      this.CPllStandby = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllStandby::type_id::create("CPllStandby",,get_full_name());
      if(this.CPllStandby.has_coverage(UVM_CVR_ALL))
      	this.CPllStandby.cg_bits.option.name = {get_name(), ".", "CPllStandby_bits"};
      this.CPllStandby.configure(this, null, "");
      this.CPllStandby.build();
      this.default_map.add_reg(this.CPllStandby, `UVM_REG_ADDR_WIDTH'h1, "RW", 0);
		this.CPllStandby_CPllStandby = this.CPllStandby.CPllStandby;
      this.CPllBypassMode = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllBypassMode::type_id::create("CPllBypassMode",,get_full_name());
      if(this.CPllBypassMode.has_coverage(UVM_CVR_ALL))
      	this.CPllBypassMode.cg_bits.option.name = {get_name(), ".", "CPllBypassMode_bits"};
      this.CPllBypassMode.configure(this, null, "");
      this.CPllBypassMode.build();
      this.default_map.add_reg(this.CPllBypassMode, `UVM_REG_ADDR_WIDTH'h2, "RW", 0);
		this.CPllBypassMode_CPllBypassMode = this.CPllBypassMode.CPllBypassMode;
      this.CPllStartLock = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllStartLock::type_id::create("CPllStartLock",,get_full_name());
      if(this.CPllStartLock.has_coverage(UVM_CVR_ALL))
      	this.CPllStartLock.cg_bits.option.name = {get_name(), ".", "CPllStartLock_bits"};
      this.CPllStartLock.configure(this, null, "");
      this.CPllStartLock.build();
      this.default_map.add_reg(this.CPllStartLock, `UVM_REG_ADDR_WIDTH'h3, "RW", 0);
		this.CPllStartLock_CPllPreset = this.CPllStartLock.CPllPreset;
		this.CPllPreset = this.CPllStartLock.CPllPreset;
		this.CPllStartLock_CPllGearShift = this.CPllStartLock.CPllGearShift;
		this.CPllGearShift = this.CPllStartLock.CPllGearShift;
		this.CPllStartLock_CPllFastRelock = this.CPllStartLock.CPllFastRelock;
		this.CPllFastRelock = this.CPllStartLock.CPllFastRelock;
      this.CPllCtrl0 = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl0::type_id::create("CPllCtrl0",,get_full_name());
      if(this.CPllCtrl0.has_coverage(UVM_CVR_ALL))
      	this.CPllCtrl0.cg_bits.option.name = {get_name(), ".", "CPllCtrl0_bits"};
      this.CPllCtrl0.configure(this, null, "");
      this.CPllCtrl0.build();
      this.default_map.add_reg(this.CPllCtrl0, `UVM_REG_ADDR_WIDTH'h4, "RW", 0);
		this.CPllCtrl0_CPllLockCntSel = this.CPllCtrl0.CPllLockCntSel;
		this.CPllLockCntSel = this.CPllCtrl0.CPllLockCntSel;
		this.CPllCtrl0_CReservedPllLockCntSel = this.CPllCtrl0.CReservedPllLockCntSel;
		this.CReservedPllLockCntSel = this.CPllCtrl0.CReservedPllLockCntSel;
		this.CPllCtrl0_CPllLockPhSel = this.CPllCtrl0.CPllLockPhSel;
		this.CPllLockPhSel = this.CPllCtrl0.CPllLockPhSel;
      this.CPllCtrl1_p0 = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl1_p0::type_id::create("CPllCtrl1_p0",,get_full_name());
      if(this.CPllCtrl1_p0.has_coverage(UVM_CVR_ALL))
      	this.CPllCtrl1_p0.cg_bits.option.name = {get_name(), ".", "CPllCtrl1_p0_bits"};
      this.CPllCtrl1_p0.configure(this, null, "");
      this.CPllCtrl1_p0.build();
      this.default_map.add_reg(this.CPllCtrl1_p0, `UVM_REG_ADDR_WIDTH'h5, "RW", 0);
		this.CPllCtrl1_p0_CPllCpIntCtrl = this.CPllCtrl1_p0.CPllCpIntCtrl;
		this.CPllCpIntCtrl = this.CPllCtrl1_p0.CPllCpIntCtrl;
		this.CPllCtrl1_p0_CReservedPllCpIntCtrl = this.CPllCtrl1_p0.CReservedPllCpIntCtrl;
		this.CReservedPllCpIntCtrl = this.CPllCtrl1_p0.CReservedPllCpIntCtrl;
		this.CPllCtrl1_p0_CPllCpPropCtrl = this.CPllCtrl1_p0.CPllCpPropCtrl;
		this.CPllCpPropCtrl = this.CPllCtrl1_p0.CPllCpPropCtrl;
      this.CPllCtrl3 = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl3::type_id::create("CPllCtrl3",,get_full_name());
      if(this.CPllCtrl3.has_coverage(UVM_CVR_ALL))
      	this.CPllCtrl3.cg_bits.option.name = {get_name(), ".", "CPllCtrl3_bits"};
      this.CPllCtrl3.configure(this, null, "");
      this.CPllCtrl3.build();
      this.default_map.add_reg(this.CPllCtrl3, `UVM_REG_ADDR_WIDTH'h6, "RW", 0);
		this.CPllCtrl3_CReservedPllCtrl3 = this.CPllCtrl3.CReservedPllCtrl3;
		this.CReservedPllCtrl3 = this.CPllCtrl3.CReservedPllCtrl3;
		this.CPllCtrl3_CPllMaxRange = this.CPllCtrl3.CPllMaxRange;
		this.CPllMaxRange = this.CPllCtrl3.CPllMaxRange;
		this.CPllCtrl3_CPllForceCal = this.CPllCtrl3.CPllForceCal;
		this.CPllForceCal = this.CPllCtrl3.CPllForceCal;
		this.CPllCtrl3_CPllEnCal = this.CPllCtrl3.CPllEnCal;
		this.CPllEnCal = this.CPllCtrl3.CPllEnCal;
      this.CPllCtrl4_p0 = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl4_p0::type_id::create("CPllCtrl4_p0",,get_full_name());
      if(this.CPllCtrl4_p0.has_coverage(UVM_CVR_ALL))
      	this.CPllCtrl4_p0.cg_bits.option.name = {get_name(), ".", "CPllCtrl4_p0_bits"};
      this.CPllCtrl4_p0.configure(this, null, "");
      this.CPllCtrl4_p0.build();
      this.default_map.add_reg(this.CPllCtrl4_p0, `UVM_REG_ADDR_WIDTH'h7, "RW", 0);
		this.CPllCtrl4_p0_CPllCpIntGsCtrl = this.CPllCtrl4_p0.CPllCpIntGsCtrl;
		this.CPllCpIntGsCtrl = this.CPllCtrl4_p0.CPllCpIntGsCtrl;
		this.CPllCtrl4_p0_CReservedPllCpIntGsCtrl = this.CPllCtrl4_p0.CReservedPllCpIntGsCtrl;
		this.CReservedPllCpIntGsCtrl = this.CPllCtrl4_p0.CReservedPllCpIntGsCtrl;
		this.CPllCtrl4_p0_CPllCpPropGsCtrl = this.CPllCtrl4_p0.CPllCpPropGsCtrl;
		this.CPllCpPropGsCtrl = this.CPllCtrl4_p0.CPllCpPropGsCtrl;
      this.CPllCtrl5_p0 = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllCtrl5_p0::type_id::create("CPllCtrl5_p0",,get_full_name());
      if(this.CPllCtrl5_p0.has_coverage(UVM_CVR_ALL))
      	this.CPllCtrl5_p0.cg_bits.option.name = {get_name(), ".", "CPllCtrl5_p0_bits"};
      this.CPllCtrl5_p0.configure(this, null, "");
      this.CPllCtrl5_p0.build();
      this.default_map.add_reg(this.CPllCtrl5_p0, `UVM_REG_ADDR_WIDTH'h8, "RW", 0);
		this.CPllCtrl5_p0_CPllDivSel = this.CPllCtrl5_p0.CPllDivSel;
		this.CPllDivSel = this.CPllCtrl5_p0.CPllDivSel;
		this.CPllCtrl5_p0_CPllV2IMode = this.CPllCtrl5_p0.CPllV2IMode;
		this.CPllV2IMode = this.CPllCtrl5_p0.CPllV2IMode;
		this.CPllCtrl5_p0_CPllVcoLowFreq = this.CPllCtrl5_p0.CPllVcoLowFreq;
		this.CPllVcoLowFreq = this.CPllCtrl5_p0.CPllVcoLowFreq;
      this.CPllDacValIn_p0 = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllDacValIn_p0::type_id::create("CPllDacValIn_p0",,get_full_name());
      if(this.CPllDacValIn_p0.has_coverage(UVM_CVR_ALL))
      	this.CPllDacValIn_p0.cg_bits.option.name = {get_name(), ".", "CPllDacValIn_p0_bits"};
      this.CPllDacValIn_p0.configure(this, null, "");
      this.CPllDacValIn_p0.build();
      this.default_map.add_reg(this.CPllDacValIn_p0, `UVM_REG_ADDR_WIDTH'h9, "RW", 0);
		this.CPllDacValIn_p0_CPllDacValIn_p0 = this.CPllDacValIn_p0.CPllDacValIn_p0;
      this.CMasterReserved_p0 = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CMasterReserved_p0::type_id::create("CMasterReserved_p0",,get_full_name());
      if(this.CMasterReserved_p0.has_coverage(UVM_CVR_ALL))
      	this.CMasterReserved_p0.cg_bits.option.name = {get_name(), ".", "CMasterReserved_p0_bits"};
      this.CMasterReserved_p0.configure(this, null, "");
      this.CMasterReserved_p0.build();
      this.default_map.add_reg(this.CMasterReserved_p0, `UVM_REG_ADDR_WIDTH'hA, "RW", 0);
		this.CMasterReserved_p0_CMasterReserved_p0 = this.CMasterReserved_p0.CMasterReserved_p0;
      this.CPllTst = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllTst::type_id::create("CPllTst",,get_full_name());
      if(this.CPllTst.has_coverage(UVM_CVR_ALL))
      	this.CPllTst.cg_bits.option.name = {get_name(), ".", "CPllTst_bits"};
      this.CPllTst.configure(this, null, "");
      this.CPllTst.build();
      this.default_map.add_reg(this.CPllTst, `UVM_REG_ADDR_WIDTH'hB, "RW", 0);
		this.CPllTst_CPllAnaTstEn = this.CPllTst.CPllAnaTstEn;
		this.CPllAnaTstEn = this.CPllTst.CPllAnaTstEn;
		this.CPllTst_CPllAnaTstSel = this.CPllTst.CPllAnaTstSel;
		this.CPllAnaTstSel = this.CPllTst.CPllAnaTstSel;
		this.CPllTst_CPllDigTstSel = this.CPllTst.CPllDigTstSel;
		this.CPllDigTstSel = this.CPllTst.CPllDigTstSel;
      this.CPllLockStatus = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockStatus::type_id::create("CPllLockStatus",,get_full_name());
      if(this.CPllLockStatus.has_coverage(UVM_CVR_ALL))
      	this.CPllLockStatus.cg_bits.option.name = {get_name(), ".", "CPllLockStatus_bits"};
      this.CPllLockStatus.configure(this, null, "");
      this.CPllLockStatus.build();
      this.default_map.add_reg(this.CPllLockStatus, `UVM_REG_ADDR_WIDTH'hC, "RO", 0);
		this.CPllLockStatus_CPllLockStatus = this.CPllLockStatus.CPllLockStatus;
      this.CPllUPllProg0 = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg0::type_id::create("CPllUPllProg0",,get_full_name());
      if(this.CPllUPllProg0.has_coverage(UVM_CVR_ALL))
      	this.CPllUPllProg0.cg_bits.option.name = {get_name(), ".", "CPllUPllProg0_bits"};
      this.CPllUPllProg0.configure(this, null, "");
      this.CPllUPllProg0.build();
      this.default_map.add_reg(this.CPllUPllProg0, `UVM_REG_ADDR_WIDTH'hD, "RW", 0);
		this.CPllUPllProg0_CPllUPllProg0 = this.CPllUPllProg0.CPllUPllProg0;
      this.CPllUPllProg1 = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg1::type_id::create("CPllUPllProg1",,get_full_name());
      if(this.CPllUPllProg1.has_coverage(UVM_CVR_ALL))
      	this.CPllUPllProg1.cg_bits.option.name = {get_name(), ".", "CPllUPllProg1_bits"};
      this.CPllUPllProg1.configure(this, null, "");
      this.CPllUPllProg1.build();
      this.default_map.add_reg(this.CPllUPllProg1, `UVM_REG_ADDR_WIDTH'hE, "RW", 0);
		this.CPllUPllProg1_CPllUPllProg1 = this.CPllUPllProg1.CPllUPllProg1;
      this.CPllUPllProg2 = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg2::type_id::create("CPllUPllProg2",,get_full_name());
      if(this.CPllUPllProg2.has_coverage(UVM_CVR_ALL))
      	this.CPllUPllProg2.cg_bits.option.name = {get_name(), ".", "CPllUPllProg2_bits"};
      this.CPllUPllProg2.configure(this, null, "");
      this.CPllUPllProg2.build();
      this.default_map.add_reg(this.CPllUPllProg2, `UVM_REG_ADDR_WIDTH'hF, "RW", 0);
		this.CPllUPllProg2_CPllUPllProg2 = this.CPllUPllProg2.CPllUPllProg2;
      this.CPllUPllProg3 = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllUPllProg3::type_id::create("CPllUPllProg3",,get_full_name());
      if(this.CPllUPllProg3.has_coverage(UVM_CVR_ALL))
      	this.CPllUPllProg3.cg_bits.option.name = {get_name(), ".", "CPllUPllProg3_bits"};
      this.CPllUPllProg3.configure(this, null, "");
      this.CPllUPllProg3.build();
      this.default_map.add_reg(this.CPllUPllProg3, `UVM_REG_ADDR_WIDTH'h10, "RW", 0);
		this.CPllUPllProg3_CPllUPllProg3 = this.CPllUPllProg3.CPllUPllProg3;
      this.CPllEndofCal = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllEndofCal::type_id::create("CPllEndofCal",,get_full_name());
      if(this.CPllEndofCal.has_coverage(UVM_CVR_ALL))
      	this.CPllEndofCal.cg_bits.option.name = {get_name(), ".", "CPllEndofCal_bits"};
      this.CPllEndofCal.configure(this, null, "");
      this.CPllEndofCal.build();
      this.default_map.add_reg(this.CPllEndofCal, `UVM_REG_ADDR_WIDTH'h11, "RO", 0);
		this.CPllEndofCal_CPllEndofCal = this.CPllEndofCal.CPllEndofCal;
      this.CPllStandbyEff = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllStandbyEff::type_id::create("CPllStandbyEff",,get_full_name());
      if(this.CPllStandbyEff.has_coverage(UVM_CVR_ALL))
      	this.CPllStandbyEff.cg_bits.option.name = {get_name(), ".", "CPllStandbyEff_bits"};
      this.CPllStandbyEff.configure(this, null, "");
      this.CPllStandbyEff.build();
      this.default_map.add_reg(this.CPllStandbyEff, `UVM_REG_ADDR_WIDTH'h12, "RO", 0);
		this.CPllStandbyEff_CPllStandbyEff = this.CPllStandbyEff.CPllStandbyEff;
      this.CPllDacValOut = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllDacValOut::type_id::create("CPllDacValOut",,get_full_name());
      if(this.CPllDacValOut.has_coverage(UVM_CVR_ALL))
      	this.CPllDacValOut.cg_bits.option.name = {get_name(), ".", "CPllDacValOut_bits"};
      this.CPllDacValOut.configure(this, null, "");
      this.CPllDacValOut.build();
      this.default_map.add_reg(this.CPllDacValOut, `UVM_REG_ADDR_WIDTH'h13, "RO", 0);
		this.CPllDacValOut_CPllDacValOut = this.CPllDacValOut.CPllDacValOut;
      this.CPllLockedStatus = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockedStatus::type_id::create("CPllLockedStatus",,get_full_name());
      if(this.CPllLockedStatus.has_coverage(UVM_CVR_ALL))
      	this.CPllLockedStatus.cg_bits.option.name = {get_name(), ".", "CPllLockedStatus_bits"};
      this.CPllLockedStatus.configure(this, null, "");
      this.CPllLockedStatus.build();
      this.default_map.add_reg(this.CPllLockedStatus, `UVM_REG_ADDR_WIDTH'h14, "RO", 0);
		this.CPllLockedStatus_CPllLocked = this.CPllLockedStatus.CPllLocked;
		this.CPllLocked = this.CPllLockedStatus.CPllLocked;
		this.CPllLockedStatus_CPllUnlocked = this.CPllLockedStatus.CPllUnlocked;
		this.CPllUnlocked = this.CPllLockedStatus.CPllUnlocked;
      this.CPllLockedControl = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockedControl::type_id::create("CPllLockedControl",,get_full_name());
      if(this.CPllLockedControl.has_coverage(UVM_CVR_ALL))
      	this.CPllLockedControl.cg_bits.option.name = {get_name(), ".", "CPllLockedControl_bits"};
      this.CPllLockedControl.configure(this, null, "");
      this.CPllLockedControl.build();
      this.default_map.add_reg(this.CPllLockedControl, `UVM_REG_ADDR_WIDTH'h15, "RW", 0);
		this.CPllLockedControl_CPllLockedClear = this.CPllLockedControl.CPllLockedClear;
		this.CPllLockedClear = this.CPllLockedControl.CPllLockedClear;
		this.CPllLockedControl_CPllLockedHiCtrMode = this.CPllLockedControl.CPllLockedHiCtrMode;
		this.CPllLockedHiCtrMode = this.CPllLockedControl.CPllLockedHiCtrMode;
		this.CPllLockedControl_CPllLockedTransCtrMode = this.CPllLockedControl.CPllLockedTransCtrMode;
		this.CPllLockedTransCtrMode = this.CPllLockedControl.CPllLockedTransCtrMode;
		this.CPllLockedControl_CPllLockedCtrsEnable = this.CPllLockedControl.CPllLockedCtrsEnable;
		this.CPllLockedCtrsEnable = this.CPllLockedControl.CPllLockedCtrsEnable;
		this.CPllLockedControl_CPllLockedCtrsClear = this.CPllLockedControl.CPllLockedCtrsClear;
		this.CPllLockedCtrsClear = this.CPllLockedControl.CPllLockedCtrsClear;
      this.CPllLockedHiCtr = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockedHiCtr::type_id::create("CPllLockedHiCtr",,get_full_name());
      if(this.CPllLockedHiCtr.has_coverage(UVM_CVR_ALL))
      	this.CPllLockedHiCtr.cg_bits.option.name = {get_name(), ".", "CPllLockedHiCtr_bits"};
      this.CPllLockedHiCtr.configure(this, null, "");
      this.CPllLockedHiCtr.build();
      this.default_map.add_reg(this.CPllLockedHiCtr, `UVM_REG_ADDR_WIDTH'h16, "RO", 0);
		this.CPllLockedHiCtr_CPllLockedHiCtr = this.CPllLockedHiCtr.CPllLockedHiCtr;
      this.CPllLockedTransCtr = ral_reg_DWC_DDRPHYA_HMMAS0_p0_CPllLockedTransCtr::type_id::create("CPllLockedTransCtr",,get_full_name());
      if(this.CPllLockedTransCtr.has_coverage(UVM_CVR_ALL))
      	this.CPllLockedTransCtr.cg_bits.option.name = {get_name(), ".", "CPllLockedTransCtr_bits"};
      this.CPllLockedTransCtr.configure(this, null, "");
      this.CPllLockedTransCtr.build();
      this.default_map.add_reg(this.CPllLockedTransCtr, `UVM_REG_ADDR_WIDTH'h17, "RO", 0);
		this.CPllLockedTransCtr_CPllLockedTransCtr = this.CPllLockedTransCtr.CPllLockedTransCtr;
      this.MtestMuxSelMAS = ral_reg_DWC_DDRPHYA_HMMAS0_p0_MtestMuxSelMAS::type_id::create("MtestMuxSelMAS",,get_full_name());
      if(this.MtestMuxSelMAS.has_coverage(UVM_CVR_ALL))
      	this.MtestMuxSelMAS.cg_bits.option.name = {get_name(), ".", "MtestMuxSelMAS_bits"};
      this.MtestMuxSelMAS.configure(this, null, "");
      this.MtestMuxSelMAS.build();
      this.default_map.add_reg(this.MtestMuxSelMAS, `UVM_REG_ADDR_WIDTH'h1A, "RW", 0);
		this.MtestMuxSelMAS_MtestMuxSelMAS = this.MtestMuxSelMAS.MtestMuxSelMAS;
      this.HMPclkPtrInitVal_p0 = ral_reg_DWC_DDRPHYA_HMMAS0_p0_HMPclkPtrInitVal_p0::type_id::create("HMPclkPtrInitVal_p0",,get_full_name());
      if(this.HMPclkPtrInitVal_p0.has_coverage(UVM_CVR_ALL))
      	this.HMPclkPtrInitVal_p0.cg_bits.option.name = {get_name(), ".", "HMPclkPtrInitVal_p0_bits"};
      this.HMPclkPtrInitVal_p0.configure(this, null, "");
      this.HMPclkPtrInitVal_p0.build();
      this.default_map.add_reg(this.HMPclkPtrInitVal_p0, `UVM_REG_ADDR_WIDTH'h40, "RW", 0);
		this.HMPclkPtrInitVal_p0_HMPclkPtrInitVal_p0 = this.HMPclkPtrInitVal_p0.HMPclkPtrInitVal_p0;
      this.HMMASParityInvert = ral_reg_DWC_DDRPHYA_HMMAS0_p0_HMMASParityInvert::type_id::create("HMMASParityInvert",,get_full_name());
      if(this.HMMASParityInvert.has_coverage(UVM_CVR_ALL))
      	this.HMMASParityInvert.cg_bits.option.name = {get_name(), ".", "HMMASParityInvert_bits"};
      this.HMMASParityInvert.configure(this, null, "");
      this.HMMASParityInvert.build();
      this.default_map.add_reg(this.HMMASParityInvert, `UVM_REG_ADDR_WIDTH'h4D, "RW", 0);
		this.HMMASParityInvert_HMMASParityInvert = this.HMMASParityInvert.HMMASParityInvert;
      this.ScratchPadHMMAS = ral_reg_DWC_DDRPHYA_HMMAS0_p0_ScratchPadHMMAS::type_id::create("ScratchPadHMMAS",,get_full_name());
      if(this.ScratchPadHMMAS.has_coverage(UVM_CVR_ALL))
      	this.ScratchPadHMMAS.cg_bits.option.name = {get_name(), ".", "ScratchPadHMMAS_bits"};
      this.ScratchPadHMMAS.configure(this, null, "");
      this.ScratchPadHMMAS.build();
      this.default_map.add_reg(this.ScratchPadHMMAS, `UVM_REG_ADDR_WIDTH'h7D, "RW", 0);
		this.ScratchPadHMMAS_ScratchPadHMMAS = this.ScratchPadHMMAS.ScratchPadHMMAS;
      this.HMReserved0 = ral_reg_DWC_DDRPHYA_HMMAS0_p0_HMReserved0::type_id::create("HMReserved0",,get_full_name());
      if(this.HMReserved0.has_coverage(UVM_CVR_ALL))
      	this.HMReserved0.cg_bits.option.name = {get_name(), ".", "HMReserved0_bits"};
      this.HMReserved0.configure(this, null, "");
      this.HMReserved0.build();
      this.default_map.add_reg(this.HMReserved0, `UVM_REG_ADDR_WIDTH'hFE, "RW", 0);
		this.HMReserved0_HMReserved0 = this.HMReserved0.HMReserved0;
      this.HMReservedP1_p0 = ral_reg_DWC_DDRPHYA_HMMAS0_p0_HMReservedP1_p0::type_id::create("HMReservedP1_p0",,get_full_name());
      if(this.HMReservedP1_p0.has_coverage(UVM_CVR_ALL))
      	this.HMReservedP1_p0.cg_bits.option.name = {get_name(), ".", "HMReservedP1_p0_bits"};
      this.HMReservedP1_p0.configure(this, null, "");
      this.HMReservedP1_p0.build();
      this.default_map.add_reg(this.HMReservedP1_p0, `UVM_REG_ADDR_WIDTH'hFF, "RW", 0);
		this.HMReservedP1_p0_HMReservedP1_p0 = this.HMReservedP1_p0.HMReservedP1_p0;
   endfunction : build

	`uvm_object_utils(ral_block_DWC_DDRPHYA_HMMAS0_p0)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_DDRPHYA_HMMAS0_p0


endpackage
`endif
