`ifndef RAL_DWC_DDRPHYA_MASTER0_P0_PKG
`define RAL_DWC_DDRPHYA_MASTER0_P0_PKG

package ral_DWC_DDRPHYA_MASTER0_p0_pkg;
import uvm_pkg::*;

class ral_reg_DWC_DDRPHYA_MASTER0_p0_DfiFreqRatio_p0 extends uvm_reg;
	rand uvm_reg_field DfiFreqRatio_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiFreqRatio_p0: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_DfiFreqRatio_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiFreqRatio_p0 = uvm_reg_field::type_id::create("DfiFreqRatio_p0",,get_full_name());
      this.DfiFreqRatio_p0.configure(this, 2, 0, "RW", 0, 2'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_DfiFreqRatio_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_DfiFreqRatio_p0


class ral_reg_DWC_DDRPHYA_MASTER0_p0_PubDxPowerDownControl extends uvm_reg;
	rand uvm_reg_field LP5DxPowerDown;
	rand uvm_reg_field D5DxPowerDown;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   LP5DxPowerDown: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   D5DxPowerDown: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_PubDxPowerDownControl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.LP5DxPowerDown = uvm_reg_field::type_id::create("LP5DxPowerDown",,get_full_name());
      this.LP5DxPowerDown.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.D5DxPowerDown = uvm_reg_field::type_id::create("D5DxPowerDown",,get_full_name());
      this.D5DxPowerDown.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_PubDxPowerDownControl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_PubDxPowerDownControl


class ral_reg_DWC_DDRPHYA_MASTER0_p0_PclkPtrInitVal_p0 extends uvm_reg;
	rand uvm_reg_field PclkPtrInitVal_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkPtrInitVal_p0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_PclkPtrInitVal_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkPtrInitVal_p0 = uvm_reg_field::type_id::create("PclkPtrInitVal_p0",,get_full_name());
      this.PclkPtrInitVal_p0.configure(this, 5, 0, "RW", 0, 5'h2, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_PclkPtrInitVal_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_PclkPtrInitVal_p0


class ral_reg_DWC_DDRPHYA_MASTER0_p0_CmdFifoWrModeMaster_p0 extends uvm_reg;
	rand uvm_reg_field CmdFifoWrModeMaster_p0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CmdFifoWrModeMaster_p0: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_CmdFifoWrModeMaster_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CmdFifoWrModeMaster_p0 = uvm_reg_field::type_id::create("CmdFifoWrModeMaster_p0",,get_full_name());
      this.CmdFifoWrModeMaster_p0.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_CmdFifoWrModeMaster_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_CmdFifoWrModeMaster_p0


class ral_reg_DWC_DDRPHYA_MASTER0_p0_MTestDtoCtrl extends uvm_reg;
	rand uvm_reg_field MTESTdtoEn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   MTESTdtoEn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_MTestDtoCtrl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MTESTdtoEn = uvm_reg_field::type_id::create("MTESTdtoEn",,get_full_name());
      this.MTESTdtoEn.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_MTestDtoCtrl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_MTestDtoCtrl


class ral_reg_DWC_DDRPHYA_MASTER0_p0_PipeCtl_p0 extends uvm_reg;
	rand uvm_reg_field DxInPipeEn;
	rand uvm_reg_field DxOutPipeEn;
	rand uvm_reg_field AlertNPipeEn;
	rand uvm_reg_field AcInPipeEn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DxInPipeEn: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   DxOutPipeEn: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   AlertNPipeEn: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   AcInPipeEn: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_PipeCtl_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DxInPipeEn = uvm_reg_field::type_id::create("DxInPipeEn",,get_full_name());
      this.DxInPipeEn.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.DxOutPipeEn = uvm_reg_field::type_id::create("DxOutPipeEn",,get_full_name());
      this.DxOutPipeEn.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.AlertNPipeEn = uvm_reg_field::type_id::create("AlertNPipeEn",,get_full_name());
      this.AlertNPipeEn.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.AcInPipeEn = uvm_reg_field::type_id::create("AcInPipeEn",,get_full_name());
      this.AcInPipeEn.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_PipeCtl_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_PipeCtl_p0


class ral_reg_DWC_DDRPHYA_MASTER0_p0_LpDqPhaseDisable extends uvm_reg;
	rand uvm_reg_field LpDqPhaseDisable;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   LpDqPhaseDisable: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_LpDqPhaseDisable");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.LpDqPhaseDisable = uvm_reg_field::type_id::create("LpDqPhaseDisable",,get_full_name());
      this.LpDqPhaseDisable.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_LpDqPhaseDisable)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_LpDqPhaseDisable


class ral_reg_DWC_DDRPHYA_MASTER0_p0_PubDbyteDisable extends uvm_reg;
	rand uvm_reg_field PubDbyteDisable;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PubDbyteDisable: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_PubDbyteDisable");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PubDbyteDisable = uvm_reg_field::type_id::create("PubDbyteDisable",,get_full_name());
      this.PubDbyteDisable.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_PubDbyteDisable)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_PubDbyteDisable


class ral_reg_DWC_DDRPHYA_MASTER0_p0_CPclkDivRatio_p0 extends uvm_reg;
	rand uvm_reg_field CPclkDivCa0;
	rand uvm_reg_field ReservedCPclkDivCa0;
	rand uvm_reg_field CPclkDivCa1;
	rand uvm_reg_field ReservedCPclkDivCa1;
	rand uvm_reg_field CPclkDivDq0;
	rand uvm_reg_field ReservedCPclkDivDq0;
	rand uvm_reg_field CPclkDivDq1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CPclkDivCa0: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   ReservedCPclkDivCa0: coverpoint {m_data[3:2], m_is_read} iff(m_be) {
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
	   CPclkDivCa1: coverpoint {m_data[5:4], m_is_read} iff(m_be) {
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
	   ReservedCPclkDivCa1: coverpoint {m_data[7:6], m_is_read} iff(m_be) {
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
	   CPclkDivDq0: coverpoint {m_data[9:8], m_is_read} iff(m_be) {
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
	   ReservedCPclkDivDq0: coverpoint {m_data[11:10], m_is_read} iff(m_be) {
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
	   CPclkDivDq1: coverpoint {m_data[13:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_CPclkDivRatio_p0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CPclkDivCa0 = uvm_reg_field::type_id::create("CPclkDivCa0",,get_full_name());
      this.CPclkDivCa0.configure(this, 2, 0, "RW", 0, 2'h1, 1, 0, 0);
      this.ReservedCPclkDivCa0 = uvm_reg_field::type_id::create("ReservedCPclkDivCa0",,get_full_name());
      this.ReservedCPclkDivCa0.configure(this, 2, 2, "RW", 0, 2'h0, 1, 0, 0);
      this.CPclkDivCa1 = uvm_reg_field::type_id::create("CPclkDivCa1",,get_full_name());
      this.CPclkDivCa1.configure(this, 2, 4, "RW", 0, 2'h1, 1, 0, 0);
      this.ReservedCPclkDivCa1 = uvm_reg_field::type_id::create("ReservedCPclkDivCa1",,get_full_name());
      this.ReservedCPclkDivCa1.configure(this, 2, 6, "RW", 0, 2'h0, 1, 0, 0);
      this.CPclkDivDq0 = uvm_reg_field::type_id::create("CPclkDivDq0",,get_full_name());
      this.CPclkDivDq0.configure(this, 2, 8, "RW", 0, 2'h1, 1, 0, 0);
      this.ReservedCPclkDivDq0 = uvm_reg_field::type_id::create("ReservedCPclkDivDq0",,get_full_name());
      this.ReservedCPclkDivDq0.configure(this, 2, 10, "RW", 0, 2'h0, 1, 0, 0);
      this.CPclkDivDq1 = uvm_reg_field::type_id::create("CPclkDivDq1",,get_full_name());
      this.CPclkDivDq1.configure(this, 2, 12, "RW", 0, 2'h1, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_CPclkDivRatio_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_CPclkDivRatio_p0


class ral_reg_DWC_DDRPHYA_MASTER0_p0_PipeNetDis extends uvm_reg;
	rand uvm_reg_field PipeNetDis;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PipeNetDis: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_PipeNetDis");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PipeNetDis = uvm_reg_field::type_id::create("PipeNetDis",,get_full_name());
      this.PipeNetDis.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_PipeNetDis)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_PipeNetDis


class ral_reg_DWC_DDRPHYA_MASTER0_p0_MiscPipeEn extends uvm_reg;
	rand uvm_reg_field MiscPipeEn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   MiscPipeEn: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_MiscPipeEn");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MiscPipeEn = uvm_reg_field::type_id::create("MiscPipeEn",,get_full_name());
      this.MiscPipeEn.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_MiscPipeEn)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_MiscPipeEn


class ral_reg_DWC_DDRPHYA_MASTER0_p0_MtestMuxSelCMOS extends uvm_reg;
	rand uvm_reg_field MtestMuxSelCMOS;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   MtestMuxSelCMOS: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_MtestMuxSelCMOS");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MtestMuxSelCMOS = uvm_reg_field::type_id::create("MtestMuxSelCMOS",,get_full_name());
      this.MtestMuxSelCMOS.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_MtestMuxSelCMOS)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_MtestMuxSelCMOS


class ral_reg_DWC_DDRPHYA_MASTER0_p0_EnRxDqsTracking_p0 extends uvm_reg;
	rand uvm_reg_field EnRxDqsTrackingPipe;
	rand uvm_reg_field EnDqsSampNegRxEnPPT;
	rand uvm_reg_field DqsSampNegRxEnSense;
	rand uvm_reg_field EnDqsSampNegRxEn;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   EnRxDqsTrackingPipe: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   EnDqsSampNegRxEnPPT: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   DqsSampNegRxEnSense: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   EnDqsSampNegRxEn: coverpoint {m_data[3:3], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_EnRxDqsTracking_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.EnRxDqsTrackingPipe = uvm_reg_field::type_id::create("EnRxDqsTrackingPipe",,get_full_name());
      this.EnRxDqsTrackingPipe.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.EnDqsSampNegRxEnPPT = uvm_reg_field::type_id::create("EnDqsSampNegRxEnPPT",,get_full_name());
      this.EnDqsSampNegRxEnPPT.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.DqsSampNegRxEnSense = uvm_reg_field::type_id::create("DqsSampNegRxEnSense",,get_full_name());
      this.DqsSampNegRxEnSense.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
      this.EnDqsSampNegRxEn = uvm_reg_field::type_id::create("EnDqsSampNegRxEn",,get_full_name());
      this.EnDqsSampNegRxEn.configure(this, 1, 3, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_EnRxDqsTracking_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_EnRxDqsTracking_p0


class ral_reg_DWC_DDRPHYA_MASTER0_p0_MtestMuxSel extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_MtestMuxSel");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MtestMuxSel = uvm_reg_field::type_id::create("MtestMuxSel",,get_full_name());
      this.MtestMuxSel.configure(this, 10, 0, "RW", 0, 10'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_MtestMuxSel)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_MtestMuxSel


class ral_reg_DWC_DDRPHYA_MASTER0_p0_MASTERParityInvert extends uvm_reg;
	rand uvm_reg_field MASTERParityInvert;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   MASTERParityInvert: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_MASTERParityInvert");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MASTERParityInvert = uvm_reg_field::type_id::create("MASTERParityInvert",,get_full_name());
      this.MASTERParityInvert.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_MASTERParityInvert)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_MASTERParityInvert


class ral_reg_DWC_DDRPHYA_MASTER0_p0_DfiMode extends uvm_reg;
	rand uvm_reg_field Dfi0Enable;
	rand uvm_reg_field Dfi1Enable;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   Dfi0Enable: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   Dfi1Enable: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_DfiMode");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.Dfi0Enable = uvm_reg_field::type_id::create("Dfi0Enable",,get_full_name());
      this.Dfi0Enable.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 0);
      this.Dfi1Enable = uvm_reg_field::type_id::create("Dfi1Enable",,get_full_name());
      this.Dfi1Enable.configure(this, 1, 1, "RW", 0, 1'h1, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_DfiMode)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_DfiMode


class ral_reg_DWC_DDRPHYA_MASTER0_p0_MtestPgmInfo extends uvm_reg;
	rand uvm_reg_field MtestPgmInfo;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   MtestPgmInfo: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_MtestPgmInfo");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MtestPgmInfo = uvm_reg_field::type_id::create("MtestPgmInfo",,get_full_name());
      this.MtestPgmInfo.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_MtestPgmInfo)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_MtestPgmInfo


class ral_reg_DWC_DDRPHYA_MASTER0_p0_PhyTID extends uvm_reg;
	rand uvm_reg_field PhyTID;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PhyTID: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_PhyTID");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PhyTID = uvm_reg_field::type_id::create("PhyTID",,get_full_name());
      this.PhyTID.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_PhyTID)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_PhyTID


class ral_reg_DWC_DDRPHYA_MASTER0_p0_DbyteRxEnTrain extends uvm_reg;
	rand uvm_reg_field DbyteRxEnTrain;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DbyteRxEnTrain: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_DbyteRxEnTrain");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DbyteRxEnTrain = uvm_reg_field::type_id::create("DbyteRxEnTrain",,get_full_name());
      this.DbyteRxEnTrain.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_DbyteRxEnTrain)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_DbyteRxEnTrain


class ral_reg_DWC_DDRPHYA_MASTER0_p0_PUBMODE extends uvm_reg;
	rand uvm_reg_field HwtMemSrc;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HwtMemSrc: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_PUBMODE");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HwtMemSrc = uvm_reg_field::type_id::create("HwtMemSrc",,get_full_name());
      this.HwtMemSrc.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_PUBMODE)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_PUBMODE


class ral_reg_DWC_DDRPHYA_MASTER0_p0_DllTrainParam_p0 extends uvm_reg;
	rand uvm_reg_field ExtendPhdTime;
	rand uvm_reg_field RxReplicaExtendPhdTime;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ExtendPhdTime: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   RxReplicaExtendPhdTime: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_DllTrainParam_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ExtendPhdTime = uvm_reg_field::type_id::create("ExtendPhdTime",,get_full_name());
      this.ExtendPhdTime.configure(this, 4, 0, "RW", 0, 4'hf, 1, 0, 0);
      this.RxReplicaExtendPhdTime = uvm_reg_field::type_id::create("RxReplicaExtendPhdTime",,get_full_name());
      this.RxReplicaExtendPhdTime.configure(this, 4, 4, "RW", 0, 4'hf, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_DllTrainParam_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_DllTrainParam_p0


class ral_reg_DWC_DDRPHYA_MASTER0_p0_DllControl extends uvm_reg;
	rand uvm_reg_field DllResetRelock;
	rand uvm_reg_field DllResetSlave;
	rand uvm_reg_field DllResetRSVD;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DllResetRelock: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   DllResetSlave: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   DllResetRSVD: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_DllControl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DllResetRelock = uvm_reg_field::type_id::create("DllResetRelock",,get_full_name());
      this.DllResetRelock.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.DllResetSlave = uvm_reg_field::type_id::create("DllResetSlave",,get_full_name());
      this.DllResetSlave.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.DllResetRSVD = uvm_reg_field::type_id::create("DllResetRSVD",,get_full_name());
      this.DllResetRSVD.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_DllControl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_DllControl


class ral_reg_DWC_DDRPHYA_MASTER0_p0_PulseDllUpdatePhase extends uvm_reg;
	rand uvm_reg_field PulseDllUpdatePhase;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PulseDllUpdatePhase: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_PulseDllUpdatePhase");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PulseDllUpdatePhase = uvm_reg_field::type_id::create("PulseDllUpdatePhase",,get_full_name());
      this.PulseDllUpdatePhase.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_PulseDllUpdatePhase)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_PulseDllUpdatePhase


class ral_reg_DWC_DDRPHYA_MASTER0_p0_ScratchPadMASTER extends uvm_reg;
	rand uvm_reg_field ScratchPadMASTER;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ScratchPadMASTER: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_ScratchPadMASTER");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ScratchPadMASTER = uvm_reg_field::type_id::create("ScratchPadMASTER",,get_full_name());
      this.ScratchPadMASTER.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_ScratchPadMASTER)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_ScratchPadMASTER


class ral_reg_DWC_DDRPHYA_MASTER0_p0_PState extends uvm_reg;
	rand uvm_reg_field PState;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PState: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_PState");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PState = uvm_reg_field::type_id::create("PState",,get_full_name());
      this.PState.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_PState)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_PState


class ral_reg_DWC_DDRPHYA_MASTER0_p0_RxFifoInit extends uvm_reg;
	rand uvm_reg_field RxFifoInitPtr;
	rand uvm_reg_field InhibitRxFifoRd;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxFifoInitPtr: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   InhibitRxFifoRd: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_RxFifoInit");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxFifoInitPtr = uvm_reg_field::type_id::create("RxFifoInitPtr",,get_full_name());
      this.RxFifoInitPtr.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.InhibitRxFifoRd = uvm_reg_field::type_id::create("InhibitRxFifoRd",,get_full_name());
      this.InhibitRxFifoRd.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_RxFifoInit)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_RxFifoInit


class ral_reg_DWC_DDRPHYA_MASTER0_p0_ClockingCtrl extends uvm_reg;
	rand uvm_reg_field ClockingCtrl;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ClockingCtrl: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_ClockingCtrl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ClockingCtrl = uvm_reg_field::type_id::create("ClockingCtrl",,get_full_name());
      this.ClockingCtrl.configure(this, 2, 0, "RW", 0, 2'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_ClockingCtrl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_ClockingCtrl


class ral_reg_DWC_DDRPHYA_MASTER0_p0_PhyPipeConfig extends uvm_reg;
	uvm_reg_field PhyConfigPipeWr;
	uvm_reg_field PhyConfigPipeRd;
	uvm_reg_field PhyConfigPipeMisc;
	uvm_reg_field PhyConfigPipeSideband;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PhyConfigPipeWr: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	   PhyConfigPipeRd: coverpoint {m_data[5:3], m_is_read} iff(m_be) {
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
	   PhyConfigPipeMisc: coverpoint {m_data[8:6], m_is_read} iff(m_be) {
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
	   PhyConfigPipeSideband: coverpoint {m_data[11:9], m_is_read} iff(m_be) {
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
	endgroup
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_PhyPipeConfig");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PhyConfigPipeWr = uvm_reg_field::type_id::create("PhyConfigPipeWr",,get_full_name());
      this.PhyConfigPipeWr.configure(this, 3, 0, "RO", 1, 3'h0, 1, 0, 0);
      this.PhyConfigPipeRd = uvm_reg_field::type_id::create("PhyConfigPipeRd",,get_full_name());
      this.PhyConfigPipeRd.configure(this, 3, 3, "RO", 1, 3'h0, 1, 0, 0);
      this.PhyConfigPipeMisc = uvm_reg_field::type_id::create("PhyConfigPipeMisc",,get_full_name());
      this.PhyConfigPipeMisc.configure(this, 3, 6, "RO", 1, 3'h0, 1, 0, 0);
      this.PhyConfigPipeSideband = uvm_reg_field::type_id::create("PhyConfigPipeSideband",,get_full_name());
      this.PhyConfigPipeSideband.configure(this, 3, 9, "RO", 1, 3'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_PhyPipeConfig)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_PhyPipeConfig


class ral_reg_DWC_DDRPHYA_MASTER0_p0_PhyConfig extends uvm_reg;
	uvm_reg_field PhyConfigDbytes;
	uvm_reg_field PhyConfigDfi;
	uvm_reg_field PhyConfigRank;
	uvm_reg_field PhyConfigDmi;
	uvm_reg_field PhyConfigLp5;
	uvm_reg_field PhyConfigLp4;
	uvm_reg_field PhyConfigDTO;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PhyConfigDbytes: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {5'b???00};
	      wildcard bins bit_0_wr_as_1 = {5'b???10};
	      wildcard bins bit_0_rd = {5'b????1};
	      wildcard bins bit_1_wr_as_0 = {5'b??0?0};
	      wildcard bins bit_1_wr_as_1 = {5'b??1?0};
	      wildcard bins bit_1_rd = {5'b????1};
	      wildcard bins bit_2_wr_as_0 = {5'b?0??0};
	      wildcard bins bit_2_wr_as_1 = {5'b?1??0};
	      wildcard bins bit_2_rd = {5'b????1};
	      wildcard bins bit_3_wr_as_0 = {5'b0???0};
	      wildcard bins bit_3_wr_as_1 = {5'b1???0};
	      wildcard bins bit_3_rd = {5'b????1};
	      option.weight = 12;
	   }
	   PhyConfigDfi: coverpoint {m_data[5:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {3'b?00};
	      wildcard bins bit_0_wr_as_1 = {3'b?10};
	      wildcard bins bit_0_rd = {3'b??1};
	      wildcard bins bit_1_wr_as_0 = {3'b0?0};
	      wildcard bins bit_1_wr_as_1 = {3'b1?0};
	      wildcard bins bit_1_rd = {3'b??1};
	      option.weight = 6;
	   }
	   PhyConfigRank: coverpoint {m_data[8:6], m_is_read} iff(m_be) {
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
	   PhyConfigDmi: coverpoint {m_data[9:9], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   PhyConfigLp5: coverpoint {m_data[10:10], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   PhyConfigLp4: coverpoint {m_data[11:11], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   PhyConfigDTO: coverpoint {m_data[12:12], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_PhyConfig");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PhyConfigDbytes = uvm_reg_field::type_id::create("PhyConfigDbytes",,get_full_name());
      this.PhyConfigDbytes.configure(this, 4, 0, "RO", 1, 4'h0, 1, 0, 0);
      this.PhyConfigDfi = uvm_reg_field::type_id::create("PhyConfigDfi",,get_full_name());
      this.PhyConfigDfi.configure(this, 2, 4, "RO", 1, 2'h0, 1, 0, 0);
      this.PhyConfigRank = uvm_reg_field::type_id::create("PhyConfigRank",,get_full_name());
      this.PhyConfigRank.configure(this, 3, 6, "RO", 1, 3'h0, 1, 0, 0);
      this.PhyConfigDmi = uvm_reg_field::type_id::create("PhyConfigDmi",,get_full_name());
      this.PhyConfigDmi.configure(this, 1, 9, "RO", 1, 1'h0, 1, 0, 0);
      this.PhyConfigLp5 = uvm_reg_field::type_id::create("PhyConfigLp5",,get_full_name());
      this.PhyConfigLp5.configure(this, 1, 10, "RO", 1, 1'h0, 1, 0, 0);
      this.PhyConfigLp4 = uvm_reg_field::type_id::create("PhyConfigLp4",,get_full_name());
      this.PhyConfigLp4.configure(this, 1, 11, "RO", 1, 1'h0, 1, 0, 0);
      this.PhyConfigDTO = uvm_reg_field::type_id::create("PhyConfigDTO",,get_full_name());
      this.PhyConfigDTO.configure(this, 1, 12, "RO", 1, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_PhyConfig)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_PhyConfig


class ral_reg_DWC_DDRPHYA_MASTER0_p0_LP5Mode extends uvm_reg;
	rand uvm_reg_field LP5Mode;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   LP5Mode: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_LP5Mode");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.LP5Mode = uvm_reg_field::type_id::create("LP5Mode",,get_full_name());
      this.LP5Mode.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_LP5Mode)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_LP5Mode


class ral_reg_DWC_DDRPHYA_MASTER0_p0_ForceClkGaterEnables extends uvm_reg;
	rand uvm_reg_field ForcePubDxClkEnHigh;
	rand uvm_reg_field ForcePubDxClkEnLow;
	rand uvm_reg_field ForceClkGaterEnablesReserved;
	rand uvm_reg_field ForceMasterPipeClkEnHigh;
	rand uvm_reg_field ForceCfgBusPipeClkEnHigh;
	rand uvm_reg_field ForceHCLKPipeClkEnHigh;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ForcePubDxClkEnHigh: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ForcePubDxClkEnLow: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ForceClkGaterEnablesReserved: coverpoint {m_data[5:2], m_is_read} iff(m_be) {
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
	   ForceMasterPipeClkEnHigh: coverpoint {m_data[6:6], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ForceCfgBusPipeClkEnHigh: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ForceHCLKPipeClkEnHigh: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_ForceClkGaterEnables");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ForcePubDxClkEnHigh = uvm_reg_field::type_id::create("ForcePubDxClkEnHigh",,get_full_name());
      this.ForcePubDxClkEnHigh.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.ForcePubDxClkEnLow = uvm_reg_field::type_id::create("ForcePubDxClkEnLow",,get_full_name());
      this.ForcePubDxClkEnLow.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.ForceClkGaterEnablesReserved = uvm_reg_field::type_id::create("ForceClkGaterEnablesReserved",,get_full_name());
      this.ForceClkGaterEnablesReserved.configure(this, 4, 2, "RW", 0, 4'h0, 1, 0, 0);
      this.ForceMasterPipeClkEnHigh = uvm_reg_field::type_id::create("ForceMasterPipeClkEnHigh",,get_full_name());
      this.ForceMasterPipeClkEnHigh.configure(this, 1, 6, "RW", 0, 1'h0, 1, 0, 0);
      this.ForceCfgBusPipeClkEnHigh = uvm_reg_field::type_id::create("ForceCfgBusPipeClkEnHigh",,get_full_name());
      this.ForceCfgBusPipeClkEnHigh.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ForceHCLKPipeClkEnHigh = uvm_reg_field::type_id::create("ForceHCLKPipeClkEnHigh",,get_full_name());
      this.ForceHCLKPipeClkEnHigh.configure(this, 1, 8, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_ForceClkGaterEnables)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_ForceClkGaterEnables


class ral_reg_DWC_DDRPHYA_MASTER0_p0_D5Mode extends uvm_reg;
	rand uvm_reg_field D5Mode;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   D5Mode: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_D5Mode");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.D5Mode = uvm_reg_field::type_id::create("D5Mode",,get_full_name());
      this.D5Mode.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_D5Mode)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_D5Mode


class ral_reg_DWC_DDRPHYA_MASTER0_p0_PHYREV extends uvm_reg;
	uvm_reg_field PHYREV;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PHYREV: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_PHYREV");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PHYREV = uvm_reg_field::type_id::create("PHYREV",,get_full_name());
      this.PHYREV.configure(this, 16, 0, "RO", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_PHYREV)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_PHYREV


class ral_reg_DWC_DDRPHYA_MASTER0_p0_TxRdPtrInit extends uvm_reg;
	rand uvm_reg_field TxRdPtrInit;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxRdPtrInit: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_TxRdPtrInit");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxRdPtrInit = uvm_reg_field::type_id::create("TxRdPtrInit",,get_full_name());
      this.TxRdPtrInit.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_TxRdPtrInit)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_TxRdPtrInit


class ral_reg_DWC_DDRPHYA_MASTER0_p0_MASTERReserved0 extends uvm_reg;
	rand uvm_reg_field MASTERReserved0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   MASTERReserved0: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_MASTERReserved0");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.MASTERReserved0 = uvm_reg_field::type_id::create("MASTERReserved0",,get_full_name());
      this.MASTERReserved0.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_MASTERReserved0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_MASTERReserved0


class ral_reg_DWC_DDRPHYA_MASTER0_p0_PUBReservedP1_p0 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_PUBReservedP1_p0");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PUBReservedP1_p0 = uvm_reg_field::type_id::create("PUBReservedP1_p0",,get_full_name());
      this.PUBReservedP1_p0.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_PUBReservedP1_p0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_PUBReservedP1_p0


class ral_reg_DWC_DDRPHYA_MASTER0_p0_PclkGateControl extends uvm_reg;
	rand uvm_reg_field PclkEn0;
	rand uvm_reg_field ReservedPclkEn0;
	rand uvm_reg_field PclkEn1;
	rand uvm_reg_field ReservedPclkEn1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkEn0: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   ReservedPclkEn0: coverpoint {m_data[3:2], m_is_read} iff(m_be) {
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
	   PclkEn1: coverpoint {m_data[5:4], m_is_read} iff(m_be) {
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
	   ReservedPclkEn1: coverpoint {m_data[7:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p0_PclkGateControl");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkEn0 = uvm_reg_field::type_id::create("PclkEn0",,get_full_name());
      this.PclkEn0.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 0);
      this.ReservedPclkEn0 = uvm_reg_field::type_id::create("ReservedPclkEn0",,get_full_name());
      this.ReservedPclkEn0.configure(this, 2, 2, "RW", 0, 2'h0, 1, 0, 0);
      this.PclkEn1 = uvm_reg_field::type_id::create("PclkEn1",,get_full_name());
      this.PclkEn1.configure(this, 2, 4, "RW", 0, 2'h0, 1, 0, 0);
      this.ReservedPclkEn1 = uvm_reg_field::type_id::create("ReservedPclkEn1",,get_full_name());
      this.ReservedPclkEn1.configure(this, 2, 6, "RW", 0, 2'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p0_PclkGateControl)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p0_PclkGateControl


class ral_block_DWC_DDRPHYA_MASTER0_p0 extends uvm_reg_block;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_DfiFreqRatio_p0 DfiFreqRatio_p0;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_PubDxPowerDownControl PubDxPowerDownControl;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_PclkPtrInitVal_p0 PclkPtrInitVal_p0;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_CmdFifoWrModeMaster_p0 CmdFifoWrModeMaster_p0;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_MTestDtoCtrl MTestDtoCtrl;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_PipeCtl_p0 PipeCtl_p0;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_LpDqPhaseDisable LpDqPhaseDisable;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_PubDbyteDisable PubDbyteDisable;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_CPclkDivRatio_p0 CPclkDivRatio_p0;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_PipeNetDis PipeNetDis;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_MiscPipeEn MiscPipeEn;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_MtestMuxSelCMOS MtestMuxSelCMOS;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_EnRxDqsTracking_p0 EnRxDqsTracking_p0;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_MtestMuxSel MtestMuxSel;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_MASTERParityInvert MASTERParityInvert;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_DfiMode DfiMode;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_MtestPgmInfo MtestPgmInfo;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_PhyTID PhyTID;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_DbyteRxEnTrain DbyteRxEnTrain;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_PUBMODE PUBMODE;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_DllTrainParam_p0 DllTrainParam_p0;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_DllControl DllControl;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_PulseDllUpdatePhase PulseDllUpdatePhase;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_ScratchPadMASTER ScratchPadMASTER;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_PState PState;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_RxFifoInit RxFifoInit;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_ClockingCtrl ClockingCtrl;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_PhyPipeConfig PhyPipeConfig;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_PhyConfig PhyConfig;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_LP5Mode LP5Mode;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_ForceClkGaterEnables ForceClkGaterEnables;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_D5Mode D5Mode;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_PHYREV PHYREV;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_TxRdPtrInit TxRdPtrInit;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_MASTERReserved0 MASTERReserved0;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_PUBReservedP1_p0 PUBReservedP1_p0;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p0_PclkGateControl PclkGateControl;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field DfiFreqRatio_p0_DfiFreqRatio_p0;
	rand uvm_reg_field PubDxPowerDownControl_LP5DxPowerDown;
	rand uvm_reg_field LP5DxPowerDown;
	rand uvm_reg_field PubDxPowerDownControl_D5DxPowerDown;
	rand uvm_reg_field D5DxPowerDown;
	rand uvm_reg_field PclkPtrInitVal_p0_PclkPtrInitVal_p0;
	rand uvm_reg_field CmdFifoWrModeMaster_p0_CmdFifoWrModeMaster_p0;
	rand uvm_reg_field MTestDtoCtrl_MTESTdtoEn;
	rand uvm_reg_field MTESTdtoEn;
	rand uvm_reg_field PipeCtl_p0_DxInPipeEn;
	rand uvm_reg_field DxInPipeEn;
	rand uvm_reg_field PipeCtl_p0_DxOutPipeEn;
	rand uvm_reg_field DxOutPipeEn;
	rand uvm_reg_field PipeCtl_p0_AlertNPipeEn;
	rand uvm_reg_field AlertNPipeEn;
	rand uvm_reg_field PipeCtl_p0_AcInPipeEn;
	rand uvm_reg_field AcInPipeEn;
	rand uvm_reg_field LpDqPhaseDisable_LpDqPhaseDisable;
	rand uvm_reg_field PubDbyteDisable_PubDbyteDisable;
	rand uvm_reg_field CPclkDivRatio_p0_CPclkDivCa0;
	rand uvm_reg_field CPclkDivCa0;
	rand uvm_reg_field CPclkDivRatio_p0_ReservedCPclkDivCa0;
	rand uvm_reg_field ReservedCPclkDivCa0;
	rand uvm_reg_field CPclkDivRatio_p0_CPclkDivCa1;
	rand uvm_reg_field CPclkDivCa1;
	rand uvm_reg_field CPclkDivRatio_p0_ReservedCPclkDivCa1;
	rand uvm_reg_field ReservedCPclkDivCa1;
	rand uvm_reg_field CPclkDivRatio_p0_CPclkDivDq0;
	rand uvm_reg_field CPclkDivDq0;
	rand uvm_reg_field CPclkDivRatio_p0_ReservedCPclkDivDq0;
	rand uvm_reg_field ReservedCPclkDivDq0;
	rand uvm_reg_field CPclkDivRatio_p0_CPclkDivDq1;
	rand uvm_reg_field CPclkDivDq1;
	rand uvm_reg_field PipeNetDis_PipeNetDis;
	rand uvm_reg_field MiscPipeEn_MiscPipeEn;
	rand uvm_reg_field MtestMuxSelCMOS_MtestMuxSelCMOS;
	rand uvm_reg_field EnRxDqsTracking_p0_EnRxDqsTrackingPipe;
	rand uvm_reg_field EnRxDqsTrackingPipe;
	rand uvm_reg_field EnRxDqsTracking_p0_EnDqsSampNegRxEnPPT;
	rand uvm_reg_field EnDqsSampNegRxEnPPT;
	rand uvm_reg_field EnRxDqsTracking_p0_DqsSampNegRxEnSense;
	rand uvm_reg_field DqsSampNegRxEnSense;
	rand uvm_reg_field EnRxDqsTracking_p0_EnDqsSampNegRxEn;
	rand uvm_reg_field EnDqsSampNegRxEn;
	rand uvm_reg_field MtestMuxSel_MtestMuxSel;
	rand uvm_reg_field MASTERParityInvert_MASTERParityInvert;
	rand uvm_reg_field DfiMode_Dfi0Enable;
	rand uvm_reg_field Dfi0Enable;
	rand uvm_reg_field DfiMode_Dfi1Enable;
	rand uvm_reg_field Dfi1Enable;
	rand uvm_reg_field MtestPgmInfo_MtestPgmInfo;
	rand uvm_reg_field PhyTID_PhyTID;
	rand uvm_reg_field DbyteRxEnTrain_DbyteRxEnTrain;
	rand uvm_reg_field PUBMODE_HwtMemSrc;
	rand uvm_reg_field HwtMemSrc;
	rand uvm_reg_field DllTrainParam_p0_ExtendPhdTime;
	rand uvm_reg_field ExtendPhdTime;
	rand uvm_reg_field DllTrainParam_p0_RxReplicaExtendPhdTime;
	rand uvm_reg_field RxReplicaExtendPhdTime;
	rand uvm_reg_field DllControl_DllResetRelock;
	rand uvm_reg_field DllResetRelock;
	rand uvm_reg_field DllControl_DllResetSlave;
	rand uvm_reg_field DllResetSlave;
	rand uvm_reg_field DllControl_DllResetRSVD;
	rand uvm_reg_field DllResetRSVD;
	rand uvm_reg_field PulseDllUpdatePhase_PulseDllUpdatePhase;
	rand uvm_reg_field ScratchPadMASTER_ScratchPadMASTER;
	rand uvm_reg_field PState_PState;
	rand uvm_reg_field RxFifoInit_RxFifoInitPtr;
	rand uvm_reg_field RxFifoInitPtr;
	rand uvm_reg_field RxFifoInit_InhibitRxFifoRd;
	rand uvm_reg_field InhibitRxFifoRd;
	rand uvm_reg_field ClockingCtrl_ClockingCtrl;
	uvm_reg_field PhyPipeConfig_PhyConfigPipeWr;
	uvm_reg_field PhyConfigPipeWr;
	uvm_reg_field PhyPipeConfig_PhyConfigPipeRd;
	uvm_reg_field PhyConfigPipeRd;
	uvm_reg_field PhyPipeConfig_PhyConfigPipeMisc;
	uvm_reg_field PhyConfigPipeMisc;
	uvm_reg_field PhyPipeConfig_PhyConfigPipeSideband;
	uvm_reg_field PhyConfigPipeSideband;
	uvm_reg_field PhyConfig_PhyConfigDbytes;
	uvm_reg_field PhyConfigDbytes;
	uvm_reg_field PhyConfig_PhyConfigDfi;
	uvm_reg_field PhyConfigDfi;
	uvm_reg_field PhyConfig_PhyConfigRank;
	uvm_reg_field PhyConfigRank;
	uvm_reg_field PhyConfig_PhyConfigDmi;
	uvm_reg_field PhyConfigDmi;
	uvm_reg_field PhyConfig_PhyConfigLp5;
	uvm_reg_field PhyConfigLp5;
	uvm_reg_field PhyConfig_PhyConfigLp4;
	uvm_reg_field PhyConfigLp4;
	uvm_reg_field PhyConfig_PhyConfigDTO;
	uvm_reg_field PhyConfigDTO;
	rand uvm_reg_field LP5Mode_LP5Mode;
	rand uvm_reg_field ForceClkGaterEnables_ForcePubDxClkEnHigh;
	rand uvm_reg_field ForcePubDxClkEnHigh;
	rand uvm_reg_field ForceClkGaterEnables_ForcePubDxClkEnLow;
	rand uvm_reg_field ForcePubDxClkEnLow;
	rand uvm_reg_field ForceClkGaterEnables_ForceClkGaterEnablesReserved;
	rand uvm_reg_field ForceClkGaterEnablesReserved;
	rand uvm_reg_field ForceClkGaterEnables_ForceMasterPipeClkEnHigh;
	rand uvm_reg_field ForceMasterPipeClkEnHigh;
	rand uvm_reg_field ForceClkGaterEnables_ForceCfgBusPipeClkEnHigh;
	rand uvm_reg_field ForceCfgBusPipeClkEnHigh;
	rand uvm_reg_field ForceClkGaterEnables_ForceHCLKPipeClkEnHigh;
	rand uvm_reg_field ForceHCLKPipeClkEnHigh;
	rand uvm_reg_field D5Mode_D5Mode;
	uvm_reg_field PHYREV_PHYREV;
	rand uvm_reg_field TxRdPtrInit_TxRdPtrInit;
	rand uvm_reg_field MASTERReserved0_MASTERReserved0;
	rand uvm_reg_field PUBReservedP1_p0_PUBReservedP1_p0;
	rand uvm_reg_field PclkGateControl_PclkEn0;
	rand uvm_reg_field PclkEn0;
	rand uvm_reg_field PclkGateControl_ReservedPclkEn0;
	rand uvm_reg_field ReservedPclkEn0;
	rand uvm_reg_field PclkGateControl_PclkEn1;
	rand uvm_reg_field PclkEn1;
	rand uvm_reg_field PclkGateControl_ReservedPclkEn1;
	rand uvm_reg_field ReservedPclkEn1;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	DfiFreqRatio_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h0 };
		option.weight = 1;
	}

	PubDxPowerDownControl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1 };
		option.weight = 1;
	}

	PclkPtrInitVal_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2 };
		option.weight = 1;
	}

	CmdFifoWrModeMaster_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3 };
		option.weight = 1;
	}

	MTestDtoCtrl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4 };
		option.weight = 1;
	}

	PipeCtl_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5 };
		option.weight = 1;
	}

	LpDqPhaseDisable : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h6 };
		option.weight = 1;
	}

	PubDbyteDisable : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h7 };
		option.weight = 1;
	}

	CPclkDivRatio_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB };
		option.weight = 1;
	}

	PipeNetDis : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC };
		option.weight = 1;
	}

	MiscPipeEn : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF };
		option.weight = 1;
	}

	MtestMuxSelCMOS : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h10 };
		option.weight = 1;
	}

	EnRxDqsTracking_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h19 };
		option.weight = 1;
	}

	MtestMuxSel : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1A };
		option.weight = 1;
	}

	MASTERParityInvert : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4D };
		option.weight = 1;
	}

	DfiMode : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h51 };
		option.weight = 1;
	}

	MtestPgmInfo : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h52 };
		option.weight = 1;
	}

	PhyTID : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h55 };
		option.weight = 1;
	}

	DbyteRxEnTrain : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h59 };
		option.weight = 1;
	}

	PUBMODE : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h6E };
		option.weight = 1;
	}

	DllTrainParam_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h71 };
		option.weight = 1;
	}

	DllControl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h78 };
		option.weight = 1;
	}

	PulseDllUpdatePhase : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h79 };
		option.weight = 1;
	}

	ScratchPadMASTER : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h7D };
		option.weight = 1;
	}

	PState : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h8B };
		option.weight = 1;
	}

	RxFifoInit : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA0 };
		option.weight = 1;
	}

	ClockingCtrl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA2 };
		option.weight = 1;
	}

	PhyPipeConfig : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA3 };
		option.weight = 1;
	}

	PhyConfig : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA4 };
		option.weight = 1;
	}

	LP5Mode : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA5 };
		option.weight = 1;
	}

	ForceClkGaterEnables : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA6 };
		option.weight = 1;
	}

	D5Mode : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA9 };
		option.weight = 1;
	}

	PHYREV : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hEE };
		option.weight = 1;
	}

	TxRdPtrInit : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF8 };
		option.weight = 1;
	}

	MASTERReserved0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFB };
		option.weight = 1;
	}

	PUBReservedP1_p0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFF };
		option.weight = 1;
	}

	PclkGateControl : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h200 };
		option.weight = 1;
	}
endgroup
	function new(string name = "DWC_DDRPHYA_MASTER0_p0");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.DfiFreqRatio_p0 = ral_reg_DWC_DDRPHYA_MASTER0_p0_DfiFreqRatio_p0::type_id::create("DfiFreqRatio_p0",,get_full_name());
      if(this.DfiFreqRatio_p0.has_coverage(UVM_CVR_ALL))
      	this.DfiFreqRatio_p0.cg_bits.option.name = {get_name(), ".", "DfiFreqRatio_p0_bits"};
      this.DfiFreqRatio_p0.configure(this, null, "");
      this.DfiFreqRatio_p0.build();
      this.default_map.add_reg(this.DfiFreqRatio_p0, `UVM_REG_ADDR_WIDTH'h0, "RW", 0);
		this.DfiFreqRatio_p0_DfiFreqRatio_p0 = this.DfiFreqRatio_p0.DfiFreqRatio_p0;
      this.PubDxPowerDownControl = ral_reg_DWC_DDRPHYA_MASTER0_p0_PubDxPowerDownControl::type_id::create("PubDxPowerDownControl",,get_full_name());
      if(this.PubDxPowerDownControl.has_coverage(UVM_CVR_ALL))
      	this.PubDxPowerDownControl.cg_bits.option.name = {get_name(), ".", "PubDxPowerDownControl_bits"};
      this.PubDxPowerDownControl.configure(this, null, "");
      this.PubDxPowerDownControl.build();
      this.default_map.add_reg(this.PubDxPowerDownControl, `UVM_REG_ADDR_WIDTH'h1, "RW", 0);
		this.PubDxPowerDownControl_LP5DxPowerDown = this.PubDxPowerDownControl.LP5DxPowerDown;
		this.LP5DxPowerDown = this.PubDxPowerDownControl.LP5DxPowerDown;
		this.PubDxPowerDownControl_D5DxPowerDown = this.PubDxPowerDownControl.D5DxPowerDown;
		this.D5DxPowerDown = this.PubDxPowerDownControl.D5DxPowerDown;
      this.PclkPtrInitVal_p0 = ral_reg_DWC_DDRPHYA_MASTER0_p0_PclkPtrInitVal_p0::type_id::create("PclkPtrInitVal_p0",,get_full_name());
      if(this.PclkPtrInitVal_p0.has_coverage(UVM_CVR_ALL))
      	this.PclkPtrInitVal_p0.cg_bits.option.name = {get_name(), ".", "PclkPtrInitVal_p0_bits"};
      this.PclkPtrInitVal_p0.configure(this, null, "");
      this.PclkPtrInitVal_p0.build();
      this.default_map.add_reg(this.PclkPtrInitVal_p0, `UVM_REG_ADDR_WIDTH'h2, "RW", 0);
		this.PclkPtrInitVal_p0_PclkPtrInitVal_p0 = this.PclkPtrInitVal_p0.PclkPtrInitVal_p0;
      this.CmdFifoWrModeMaster_p0 = ral_reg_DWC_DDRPHYA_MASTER0_p0_CmdFifoWrModeMaster_p0::type_id::create("CmdFifoWrModeMaster_p0",,get_full_name());
      if(this.CmdFifoWrModeMaster_p0.has_coverage(UVM_CVR_ALL))
      	this.CmdFifoWrModeMaster_p0.cg_bits.option.name = {get_name(), ".", "CmdFifoWrModeMaster_p0_bits"};
      this.CmdFifoWrModeMaster_p0.configure(this, null, "");
      this.CmdFifoWrModeMaster_p0.build();
      this.default_map.add_reg(this.CmdFifoWrModeMaster_p0, `UVM_REG_ADDR_WIDTH'h3, "RW", 0);
		this.CmdFifoWrModeMaster_p0_CmdFifoWrModeMaster_p0 = this.CmdFifoWrModeMaster_p0.CmdFifoWrModeMaster_p0;
      this.MTestDtoCtrl = ral_reg_DWC_DDRPHYA_MASTER0_p0_MTestDtoCtrl::type_id::create("MTestDtoCtrl",,get_full_name());
      if(this.MTestDtoCtrl.has_coverage(UVM_CVR_ALL))
      	this.MTestDtoCtrl.cg_bits.option.name = {get_name(), ".", "MTestDtoCtrl_bits"};
      this.MTestDtoCtrl.configure(this, null, "");
      this.MTestDtoCtrl.build();
      this.default_map.add_reg(this.MTestDtoCtrl, `UVM_REG_ADDR_WIDTH'h4, "RW", 0);
		this.MTestDtoCtrl_MTESTdtoEn = this.MTestDtoCtrl.MTESTdtoEn;
		this.MTESTdtoEn = this.MTestDtoCtrl.MTESTdtoEn;
      this.PipeCtl_p0 = ral_reg_DWC_DDRPHYA_MASTER0_p0_PipeCtl_p0::type_id::create("PipeCtl_p0",,get_full_name());
      if(this.PipeCtl_p0.has_coverage(UVM_CVR_ALL))
      	this.PipeCtl_p0.cg_bits.option.name = {get_name(), ".", "PipeCtl_p0_bits"};
      this.PipeCtl_p0.configure(this, null, "");
      this.PipeCtl_p0.build();
      this.default_map.add_reg(this.PipeCtl_p0, `UVM_REG_ADDR_WIDTH'h5, "RW", 0);
		this.PipeCtl_p0_DxInPipeEn = this.PipeCtl_p0.DxInPipeEn;
		this.DxInPipeEn = this.PipeCtl_p0.DxInPipeEn;
		this.PipeCtl_p0_DxOutPipeEn = this.PipeCtl_p0.DxOutPipeEn;
		this.DxOutPipeEn = this.PipeCtl_p0.DxOutPipeEn;
		this.PipeCtl_p0_AlertNPipeEn = this.PipeCtl_p0.AlertNPipeEn;
		this.AlertNPipeEn = this.PipeCtl_p0.AlertNPipeEn;
		this.PipeCtl_p0_AcInPipeEn = this.PipeCtl_p0.AcInPipeEn;
		this.AcInPipeEn = this.PipeCtl_p0.AcInPipeEn;
      this.LpDqPhaseDisable = ral_reg_DWC_DDRPHYA_MASTER0_p0_LpDqPhaseDisable::type_id::create("LpDqPhaseDisable",,get_full_name());
      if(this.LpDqPhaseDisable.has_coverage(UVM_CVR_ALL))
      	this.LpDqPhaseDisable.cg_bits.option.name = {get_name(), ".", "LpDqPhaseDisable_bits"};
      this.LpDqPhaseDisable.configure(this, null, "");
      this.LpDqPhaseDisable.build();
      this.default_map.add_reg(this.LpDqPhaseDisable, `UVM_REG_ADDR_WIDTH'h6, "RW", 0);
		this.LpDqPhaseDisable_LpDqPhaseDisable = this.LpDqPhaseDisable.LpDqPhaseDisable;
      this.PubDbyteDisable = ral_reg_DWC_DDRPHYA_MASTER0_p0_PubDbyteDisable::type_id::create("PubDbyteDisable",,get_full_name());
      if(this.PubDbyteDisable.has_coverage(UVM_CVR_ALL))
      	this.PubDbyteDisable.cg_bits.option.name = {get_name(), ".", "PubDbyteDisable_bits"};
      this.PubDbyteDisable.configure(this, null, "");
      this.PubDbyteDisable.build();
      this.default_map.add_reg(this.PubDbyteDisable, `UVM_REG_ADDR_WIDTH'h7, "RW", 0);
		this.PubDbyteDisable_PubDbyteDisable = this.PubDbyteDisable.PubDbyteDisable;
      this.CPclkDivRatio_p0 = ral_reg_DWC_DDRPHYA_MASTER0_p0_CPclkDivRatio_p0::type_id::create("CPclkDivRatio_p0",,get_full_name());
      if(this.CPclkDivRatio_p0.has_coverage(UVM_CVR_ALL))
      	this.CPclkDivRatio_p0.cg_bits.option.name = {get_name(), ".", "CPclkDivRatio_p0_bits"};
      this.CPclkDivRatio_p0.configure(this, null, "");
      this.CPclkDivRatio_p0.build();
      this.default_map.add_reg(this.CPclkDivRatio_p0, `UVM_REG_ADDR_WIDTH'hB, "RW", 0);
		this.CPclkDivRatio_p0_CPclkDivCa0 = this.CPclkDivRatio_p0.CPclkDivCa0;
		this.CPclkDivCa0 = this.CPclkDivRatio_p0.CPclkDivCa0;
		this.CPclkDivRatio_p0_ReservedCPclkDivCa0 = this.CPclkDivRatio_p0.ReservedCPclkDivCa0;
		this.ReservedCPclkDivCa0 = this.CPclkDivRatio_p0.ReservedCPclkDivCa0;
		this.CPclkDivRatio_p0_CPclkDivCa1 = this.CPclkDivRatio_p0.CPclkDivCa1;
		this.CPclkDivCa1 = this.CPclkDivRatio_p0.CPclkDivCa1;
		this.CPclkDivRatio_p0_ReservedCPclkDivCa1 = this.CPclkDivRatio_p0.ReservedCPclkDivCa1;
		this.ReservedCPclkDivCa1 = this.CPclkDivRatio_p0.ReservedCPclkDivCa1;
		this.CPclkDivRatio_p0_CPclkDivDq0 = this.CPclkDivRatio_p0.CPclkDivDq0;
		this.CPclkDivDq0 = this.CPclkDivRatio_p0.CPclkDivDq0;
		this.CPclkDivRatio_p0_ReservedCPclkDivDq0 = this.CPclkDivRatio_p0.ReservedCPclkDivDq0;
		this.ReservedCPclkDivDq0 = this.CPclkDivRatio_p0.ReservedCPclkDivDq0;
		this.CPclkDivRatio_p0_CPclkDivDq1 = this.CPclkDivRatio_p0.CPclkDivDq1;
		this.CPclkDivDq1 = this.CPclkDivRatio_p0.CPclkDivDq1;
      this.PipeNetDis = ral_reg_DWC_DDRPHYA_MASTER0_p0_PipeNetDis::type_id::create("PipeNetDis",,get_full_name());
      if(this.PipeNetDis.has_coverage(UVM_CVR_ALL))
      	this.PipeNetDis.cg_bits.option.name = {get_name(), ".", "PipeNetDis_bits"};
      this.PipeNetDis.configure(this, null, "");
      this.PipeNetDis.build();
      this.default_map.add_reg(this.PipeNetDis, `UVM_REG_ADDR_WIDTH'hC, "RW", 0);
		this.PipeNetDis_PipeNetDis = this.PipeNetDis.PipeNetDis;
      this.MiscPipeEn = ral_reg_DWC_DDRPHYA_MASTER0_p0_MiscPipeEn::type_id::create("MiscPipeEn",,get_full_name());
      if(this.MiscPipeEn.has_coverage(UVM_CVR_ALL))
      	this.MiscPipeEn.cg_bits.option.name = {get_name(), ".", "MiscPipeEn_bits"};
      this.MiscPipeEn.configure(this, null, "");
      this.MiscPipeEn.build();
      this.default_map.add_reg(this.MiscPipeEn, `UVM_REG_ADDR_WIDTH'hF, "RW", 0);
		this.MiscPipeEn_MiscPipeEn = this.MiscPipeEn.MiscPipeEn;
      this.MtestMuxSelCMOS = ral_reg_DWC_DDRPHYA_MASTER0_p0_MtestMuxSelCMOS::type_id::create("MtestMuxSelCMOS",,get_full_name());
      if(this.MtestMuxSelCMOS.has_coverage(UVM_CVR_ALL))
      	this.MtestMuxSelCMOS.cg_bits.option.name = {get_name(), ".", "MtestMuxSelCMOS_bits"};
      this.MtestMuxSelCMOS.configure(this, null, "");
      this.MtestMuxSelCMOS.build();
      this.default_map.add_reg(this.MtestMuxSelCMOS, `UVM_REG_ADDR_WIDTH'h10, "RW", 0);
		this.MtestMuxSelCMOS_MtestMuxSelCMOS = this.MtestMuxSelCMOS.MtestMuxSelCMOS;
      this.EnRxDqsTracking_p0 = ral_reg_DWC_DDRPHYA_MASTER0_p0_EnRxDqsTracking_p0::type_id::create("EnRxDqsTracking_p0",,get_full_name());
      if(this.EnRxDqsTracking_p0.has_coverage(UVM_CVR_ALL))
      	this.EnRxDqsTracking_p0.cg_bits.option.name = {get_name(), ".", "EnRxDqsTracking_p0_bits"};
      this.EnRxDqsTracking_p0.configure(this, null, "");
      this.EnRxDqsTracking_p0.build();
      this.default_map.add_reg(this.EnRxDqsTracking_p0, `UVM_REG_ADDR_WIDTH'h19, "RW", 0);
		this.EnRxDqsTracking_p0_EnRxDqsTrackingPipe = this.EnRxDqsTracking_p0.EnRxDqsTrackingPipe;
		this.EnRxDqsTrackingPipe = this.EnRxDqsTracking_p0.EnRxDqsTrackingPipe;
		this.EnRxDqsTracking_p0_EnDqsSampNegRxEnPPT = this.EnRxDqsTracking_p0.EnDqsSampNegRxEnPPT;
		this.EnDqsSampNegRxEnPPT = this.EnRxDqsTracking_p0.EnDqsSampNegRxEnPPT;
		this.EnRxDqsTracking_p0_DqsSampNegRxEnSense = this.EnRxDqsTracking_p0.DqsSampNegRxEnSense;
		this.DqsSampNegRxEnSense = this.EnRxDqsTracking_p0.DqsSampNegRxEnSense;
		this.EnRxDqsTracking_p0_EnDqsSampNegRxEn = this.EnRxDqsTracking_p0.EnDqsSampNegRxEn;
		this.EnDqsSampNegRxEn = this.EnRxDqsTracking_p0.EnDqsSampNegRxEn;
      this.MtestMuxSel = ral_reg_DWC_DDRPHYA_MASTER0_p0_MtestMuxSel::type_id::create("MtestMuxSel",,get_full_name());
      if(this.MtestMuxSel.has_coverage(UVM_CVR_ALL))
      	this.MtestMuxSel.cg_bits.option.name = {get_name(), ".", "MtestMuxSel_bits"};
      this.MtestMuxSel.configure(this, null, "");
      this.MtestMuxSel.build();
      this.default_map.add_reg(this.MtestMuxSel, `UVM_REG_ADDR_WIDTH'h1A, "RW", 0);
		this.MtestMuxSel_MtestMuxSel = this.MtestMuxSel.MtestMuxSel;
      this.MASTERParityInvert = ral_reg_DWC_DDRPHYA_MASTER0_p0_MASTERParityInvert::type_id::create("MASTERParityInvert",,get_full_name());
      if(this.MASTERParityInvert.has_coverage(UVM_CVR_ALL))
      	this.MASTERParityInvert.cg_bits.option.name = {get_name(), ".", "MASTERParityInvert_bits"};
      this.MASTERParityInvert.configure(this, null, "");
      this.MASTERParityInvert.build();
      this.default_map.add_reg(this.MASTERParityInvert, `UVM_REG_ADDR_WIDTH'h4D, "RW", 0);
		this.MASTERParityInvert_MASTERParityInvert = this.MASTERParityInvert.MASTERParityInvert;
      this.DfiMode = ral_reg_DWC_DDRPHYA_MASTER0_p0_DfiMode::type_id::create("DfiMode",,get_full_name());
      if(this.DfiMode.has_coverage(UVM_CVR_ALL))
      	this.DfiMode.cg_bits.option.name = {get_name(), ".", "DfiMode_bits"};
      this.DfiMode.configure(this, null, "");
      this.DfiMode.build();
      this.default_map.add_reg(this.DfiMode, `UVM_REG_ADDR_WIDTH'h51, "RW", 0);
		this.DfiMode_Dfi0Enable = this.DfiMode.Dfi0Enable;
		this.Dfi0Enable = this.DfiMode.Dfi0Enable;
		this.DfiMode_Dfi1Enable = this.DfiMode.Dfi1Enable;
		this.Dfi1Enable = this.DfiMode.Dfi1Enable;
      this.MtestPgmInfo = ral_reg_DWC_DDRPHYA_MASTER0_p0_MtestPgmInfo::type_id::create("MtestPgmInfo",,get_full_name());
      if(this.MtestPgmInfo.has_coverage(UVM_CVR_ALL))
      	this.MtestPgmInfo.cg_bits.option.name = {get_name(), ".", "MtestPgmInfo_bits"};
      this.MtestPgmInfo.configure(this, null, "");
      this.MtestPgmInfo.build();
      this.default_map.add_reg(this.MtestPgmInfo, `UVM_REG_ADDR_WIDTH'h52, "RW", 0);
		this.MtestPgmInfo_MtestPgmInfo = this.MtestPgmInfo.MtestPgmInfo;
      this.PhyTID = ral_reg_DWC_DDRPHYA_MASTER0_p0_PhyTID::type_id::create("PhyTID",,get_full_name());
      if(this.PhyTID.has_coverage(UVM_CVR_ALL))
      	this.PhyTID.cg_bits.option.name = {get_name(), ".", "PhyTID_bits"};
      this.PhyTID.configure(this, null, "");
      this.PhyTID.build();
      this.default_map.add_reg(this.PhyTID, `UVM_REG_ADDR_WIDTH'h55, "RW", 0);
		this.PhyTID_PhyTID = this.PhyTID.PhyTID;
      this.DbyteRxEnTrain = ral_reg_DWC_DDRPHYA_MASTER0_p0_DbyteRxEnTrain::type_id::create("DbyteRxEnTrain",,get_full_name());
      if(this.DbyteRxEnTrain.has_coverage(UVM_CVR_ALL))
      	this.DbyteRxEnTrain.cg_bits.option.name = {get_name(), ".", "DbyteRxEnTrain_bits"};
      this.DbyteRxEnTrain.configure(this, null, "");
      this.DbyteRxEnTrain.build();
      this.default_map.add_reg(this.DbyteRxEnTrain, `UVM_REG_ADDR_WIDTH'h59, "RW", 0);
		this.DbyteRxEnTrain_DbyteRxEnTrain = this.DbyteRxEnTrain.DbyteRxEnTrain;
      this.PUBMODE = ral_reg_DWC_DDRPHYA_MASTER0_p0_PUBMODE::type_id::create("PUBMODE",,get_full_name());
      if(this.PUBMODE.has_coverage(UVM_CVR_ALL))
      	this.PUBMODE.cg_bits.option.name = {get_name(), ".", "PUBMODE_bits"};
      this.PUBMODE.configure(this, null, "");
      this.PUBMODE.build();
      this.default_map.add_reg(this.PUBMODE, `UVM_REG_ADDR_WIDTH'h6E, "RW", 0);
		this.PUBMODE_HwtMemSrc = this.PUBMODE.HwtMemSrc;
		this.HwtMemSrc = this.PUBMODE.HwtMemSrc;
      this.DllTrainParam_p0 = ral_reg_DWC_DDRPHYA_MASTER0_p0_DllTrainParam_p0::type_id::create("DllTrainParam_p0",,get_full_name());
      if(this.DllTrainParam_p0.has_coverage(UVM_CVR_ALL))
      	this.DllTrainParam_p0.cg_bits.option.name = {get_name(), ".", "DllTrainParam_p0_bits"};
      this.DllTrainParam_p0.configure(this, null, "");
      this.DllTrainParam_p0.build();
      this.default_map.add_reg(this.DllTrainParam_p0, `UVM_REG_ADDR_WIDTH'h71, "RW", 0);
		this.DllTrainParam_p0_ExtendPhdTime = this.DllTrainParam_p0.ExtendPhdTime;
		this.ExtendPhdTime = this.DllTrainParam_p0.ExtendPhdTime;
		this.DllTrainParam_p0_RxReplicaExtendPhdTime = this.DllTrainParam_p0.RxReplicaExtendPhdTime;
		this.RxReplicaExtendPhdTime = this.DllTrainParam_p0.RxReplicaExtendPhdTime;
      this.DllControl = ral_reg_DWC_DDRPHYA_MASTER0_p0_DllControl::type_id::create("DllControl",,get_full_name());
      if(this.DllControl.has_coverage(UVM_CVR_ALL))
      	this.DllControl.cg_bits.option.name = {get_name(), ".", "DllControl_bits"};
      this.DllControl.configure(this, null, "");
      this.DllControl.build();
      this.default_map.add_reg(this.DllControl, `UVM_REG_ADDR_WIDTH'h78, "RW", 0);
		this.DllControl_DllResetRelock = this.DllControl.DllResetRelock;
		this.DllResetRelock = this.DllControl.DllResetRelock;
		this.DllControl_DllResetSlave = this.DllControl.DllResetSlave;
		this.DllResetSlave = this.DllControl.DllResetSlave;
		this.DllControl_DllResetRSVD = this.DllControl.DllResetRSVD;
		this.DllResetRSVD = this.DllControl.DllResetRSVD;
      this.PulseDllUpdatePhase = ral_reg_DWC_DDRPHYA_MASTER0_p0_PulseDllUpdatePhase::type_id::create("PulseDllUpdatePhase",,get_full_name());
      if(this.PulseDllUpdatePhase.has_coverage(UVM_CVR_ALL))
      	this.PulseDllUpdatePhase.cg_bits.option.name = {get_name(), ".", "PulseDllUpdatePhase_bits"};
      this.PulseDllUpdatePhase.configure(this, null, "");
      this.PulseDllUpdatePhase.build();
      this.default_map.add_reg(this.PulseDllUpdatePhase, `UVM_REG_ADDR_WIDTH'h79, "RW", 0);
		this.PulseDllUpdatePhase_PulseDllUpdatePhase = this.PulseDllUpdatePhase.PulseDllUpdatePhase;
      this.ScratchPadMASTER = ral_reg_DWC_DDRPHYA_MASTER0_p0_ScratchPadMASTER::type_id::create("ScratchPadMASTER",,get_full_name());
      if(this.ScratchPadMASTER.has_coverage(UVM_CVR_ALL))
      	this.ScratchPadMASTER.cg_bits.option.name = {get_name(), ".", "ScratchPadMASTER_bits"};
      this.ScratchPadMASTER.configure(this, null, "");
      this.ScratchPadMASTER.build();
      this.default_map.add_reg(this.ScratchPadMASTER, `UVM_REG_ADDR_WIDTH'h7D, "RW", 0);
		this.ScratchPadMASTER_ScratchPadMASTER = this.ScratchPadMASTER.ScratchPadMASTER;
      this.PState = ral_reg_DWC_DDRPHYA_MASTER0_p0_PState::type_id::create("PState",,get_full_name());
      if(this.PState.has_coverage(UVM_CVR_ALL))
      	this.PState.cg_bits.option.name = {get_name(), ".", "PState_bits"};
      this.PState.configure(this, null, "");
      this.PState.build();
      this.default_map.add_reg(this.PState, `UVM_REG_ADDR_WIDTH'h8B, "RW", 0);
		this.PState_PState = this.PState.PState;
      this.RxFifoInit = ral_reg_DWC_DDRPHYA_MASTER0_p0_RxFifoInit::type_id::create("RxFifoInit",,get_full_name());
      if(this.RxFifoInit.has_coverage(UVM_CVR_ALL))
      	this.RxFifoInit.cg_bits.option.name = {get_name(), ".", "RxFifoInit_bits"};
      this.RxFifoInit.configure(this, null, "");
      this.RxFifoInit.build();
      this.default_map.add_reg(this.RxFifoInit, `UVM_REG_ADDR_WIDTH'hA0, "RW", 0);
		this.RxFifoInit_RxFifoInitPtr = this.RxFifoInit.RxFifoInitPtr;
		this.RxFifoInitPtr = this.RxFifoInit.RxFifoInitPtr;
		this.RxFifoInit_InhibitRxFifoRd = this.RxFifoInit.InhibitRxFifoRd;
		this.InhibitRxFifoRd = this.RxFifoInit.InhibitRxFifoRd;
      this.ClockingCtrl = ral_reg_DWC_DDRPHYA_MASTER0_p0_ClockingCtrl::type_id::create("ClockingCtrl",,get_full_name());
      if(this.ClockingCtrl.has_coverage(UVM_CVR_ALL))
      	this.ClockingCtrl.cg_bits.option.name = {get_name(), ".", "ClockingCtrl_bits"};
      this.ClockingCtrl.configure(this, null, "");
      this.ClockingCtrl.build();
      this.default_map.add_reg(this.ClockingCtrl, `UVM_REG_ADDR_WIDTH'hA2, "RW", 0);
		this.ClockingCtrl_ClockingCtrl = this.ClockingCtrl.ClockingCtrl;
      this.PhyPipeConfig = ral_reg_DWC_DDRPHYA_MASTER0_p0_PhyPipeConfig::type_id::create("PhyPipeConfig",,get_full_name());
      if(this.PhyPipeConfig.has_coverage(UVM_CVR_ALL))
      	this.PhyPipeConfig.cg_bits.option.name = {get_name(), ".", "PhyPipeConfig_bits"};
      this.PhyPipeConfig.configure(this, null, "");
      this.PhyPipeConfig.build();
      this.default_map.add_reg(this.PhyPipeConfig, `UVM_REG_ADDR_WIDTH'hA3, "RO", 0);
		this.PhyPipeConfig_PhyConfigPipeWr = this.PhyPipeConfig.PhyConfigPipeWr;
		this.PhyConfigPipeWr = this.PhyPipeConfig.PhyConfigPipeWr;
		this.PhyPipeConfig_PhyConfigPipeRd = this.PhyPipeConfig.PhyConfigPipeRd;
		this.PhyConfigPipeRd = this.PhyPipeConfig.PhyConfigPipeRd;
		this.PhyPipeConfig_PhyConfigPipeMisc = this.PhyPipeConfig.PhyConfigPipeMisc;
		this.PhyConfigPipeMisc = this.PhyPipeConfig.PhyConfigPipeMisc;
		this.PhyPipeConfig_PhyConfigPipeSideband = this.PhyPipeConfig.PhyConfigPipeSideband;
		this.PhyConfigPipeSideband = this.PhyPipeConfig.PhyConfigPipeSideband;
      this.PhyConfig = ral_reg_DWC_DDRPHYA_MASTER0_p0_PhyConfig::type_id::create("PhyConfig",,get_full_name());
      if(this.PhyConfig.has_coverage(UVM_CVR_ALL))
      	this.PhyConfig.cg_bits.option.name = {get_name(), ".", "PhyConfig_bits"};
      this.PhyConfig.configure(this, null, "");
      this.PhyConfig.build();
      this.default_map.add_reg(this.PhyConfig, `UVM_REG_ADDR_WIDTH'hA4, "RO", 0);
		this.PhyConfig_PhyConfigDbytes = this.PhyConfig.PhyConfigDbytes;
		this.PhyConfigDbytes = this.PhyConfig.PhyConfigDbytes;
		this.PhyConfig_PhyConfigDfi = this.PhyConfig.PhyConfigDfi;
		this.PhyConfigDfi = this.PhyConfig.PhyConfigDfi;
		this.PhyConfig_PhyConfigRank = this.PhyConfig.PhyConfigRank;
		this.PhyConfigRank = this.PhyConfig.PhyConfigRank;
		this.PhyConfig_PhyConfigDmi = this.PhyConfig.PhyConfigDmi;
		this.PhyConfigDmi = this.PhyConfig.PhyConfigDmi;
		this.PhyConfig_PhyConfigLp5 = this.PhyConfig.PhyConfigLp5;
		this.PhyConfigLp5 = this.PhyConfig.PhyConfigLp5;
		this.PhyConfig_PhyConfigLp4 = this.PhyConfig.PhyConfigLp4;
		this.PhyConfigLp4 = this.PhyConfig.PhyConfigLp4;
		this.PhyConfig_PhyConfigDTO = this.PhyConfig.PhyConfigDTO;
		this.PhyConfigDTO = this.PhyConfig.PhyConfigDTO;
      this.LP5Mode = ral_reg_DWC_DDRPHYA_MASTER0_p0_LP5Mode::type_id::create("LP5Mode",,get_full_name());
      if(this.LP5Mode.has_coverage(UVM_CVR_ALL))
      	this.LP5Mode.cg_bits.option.name = {get_name(), ".", "LP5Mode_bits"};
      this.LP5Mode.configure(this, null, "");
      this.LP5Mode.build();
      this.default_map.add_reg(this.LP5Mode, `UVM_REG_ADDR_WIDTH'hA5, "RW", 0);
		this.LP5Mode_LP5Mode = this.LP5Mode.LP5Mode;
      this.ForceClkGaterEnables = ral_reg_DWC_DDRPHYA_MASTER0_p0_ForceClkGaterEnables::type_id::create("ForceClkGaterEnables",,get_full_name());
      if(this.ForceClkGaterEnables.has_coverage(UVM_CVR_ALL))
      	this.ForceClkGaterEnables.cg_bits.option.name = {get_name(), ".", "ForceClkGaterEnables_bits"};
      this.ForceClkGaterEnables.configure(this, null, "");
      this.ForceClkGaterEnables.build();
      this.default_map.add_reg(this.ForceClkGaterEnables, `UVM_REG_ADDR_WIDTH'hA6, "RW", 0);
		this.ForceClkGaterEnables_ForcePubDxClkEnHigh = this.ForceClkGaterEnables.ForcePubDxClkEnHigh;
		this.ForcePubDxClkEnHigh = this.ForceClkGaterEnables.ForcePubDxClkEnHigh;
		this.ForceClkGaterEnables_ForcePubDxClkEnLow = this.ForceClkGaterEnables.ForcePubDxClkEnLow;
		this.ForcePubDxClkEnLow = this.ForceClkGaterEnables.ForcePubDxClkEnLow;
		this.ForceClkGaterEnables_ForceClkGaterEnablesReserved = this.ForceClkGaterEnables.ForceClkGaterEnablesReserved;
		this.ForceClkGaterEnablesReserved = this.ForceClkGaterEnables.ForceClkGaterEnablesReserved;
		this.ForceClkGaterEnables_ForceMasterPipeClkEnHigh = this.ForceClkGaterEnables.ForceMasterPipeClkEnHigh;
		this.ForceMasterPipeClkEnHigh = this.ForceClkGaterEnables.ForceMasterPipeClkEnHigh;
		this.ForceClkGaterEnables_ForceCfgBusPipeClkEnHigh = this.ForceClkGaterEnables.ForceCfgBusPipeClkEnHigh;
		this.ForceCfgBusPipeClkEnHigh = this.ForceClkGaterEnables.ForceCfgBusPipeClkEnHigh;
		this.ForceClkGaterEnables_ForceHCLKPipeClkEnHigh = this.ForceClkGaterEnables.ForceHCLKPipeClkEnHigh;
		this.ForceHCLKPipeClkEnHigh = this.ForceClkGaterEnables.ForceHCLKPipeClkEnHigh;
      this.D5Mode = ral_reg_DWC_DDRPHYA_MASTER0_p0_D5Mode::type_id::create("D5Mode",,get_full_name());
      if(this.D5Mode.has_coverage(UVM_CVR_ALL))
      	this.D5Mode.cg_bits.option.name = {get_name(), ".", "D5Mode_bits"};
      this.D5Mode.configure(this, null, "");
      this.D5Mode.build();
      this.default_map.add_reg(this.D5Mode, `UVM_REG_ADDR_WIDTH'hA9, "RW", 0);
		this.D5Mode_D5Mode = this.D5Mode.D5Mode;
      this.PHYREV = ral_reg_DWC_DDRPHYA_MASTER0_p0_PHYREV::type_id::create("PHYREV",,get_full_name());
      if(this.PHYREV.has_coverage(UVM_CVR_ALL))
      	this.PHYREV.cg_bits.option.name = {get_name(), ".", "PHYREV_bits"};
      this.PHYREV.configure(this, null, "");
      this.PHYREV.build();
      this.default_map.add_reg(this.PHYREV, `UVM_REG_ADDR_WIDTH'hEE, "RO", 0);
		this.PHYREV_PHYREV = this.PHYREV.PHYREV;
      this.TxRdPtrInit = ral_reg_DWC_DDRPHYA_MASTER0_p0_TxRdPtrInit::type_id::create("TxRdPtrInit",,get_full_name());
      if(this.TxRdPtrInit.has_coverage(UVM_CVR_ALL))
      	this.TxRdPtrInit.cg_bits.option.name = {get_name(), ".", "TxRdPtrInit_bits"};
      this.TxRdPtrInit.configure(this, null, "");
      this.TxRdPtrInit.build();
      this.default_map.add_reg(this.TxRdPtrInit, `UVM_REG_ADDR_WIDTH'hF8, "RW", 0);
		this.TxRdPtrInit_TxRdPtrInit = this.TxRdPtrInit.TxRdPtrInit;
      this.MASTERReserved0 = ral_reg_DWC_DDRPHYA_MASTER0_p0_MASTERReserved0::type_id::create("MASTERReserved0",,get_full_name());
      if(this.MASTERReserved0.has_coverage(UVM_CVR_ALL))
      	this.MASTERReserved0.cg_bits.option.name = {get_name(), ".", "MASTERReserved0_bits"};
      this.MASTERReserved0.configure(this, null, "");
      this.MASTERReserved0.build();
      this.default_map.add_reg(this.MASTERReserved0, `UVM_REG_ADDR_WIDTH'hFB, "RW", 0);
		this.MASTERReserved0_MASTERReserved0 = this.MASTERReserved0.MASTERReserved0;
      this.PUBReservedP1_p0 = ral_reg_DWC_DDRPHYA_MASTER0_p0_PUBReservedP1_p0::type_id::create("PUBReservedP1_p0",,get_full_name());
      if(this.PUBReservedP1_p0.has_coverage(UVM_CVR_ALL))
      	this.PUBReservedP1_p0.cg_bits.option.name = {get_name(), ".", "PUBReservedP1_p0_bits"};
      this.PUBReservedP1_p0.configure(this, null, "");
      this.PUBReservedP1_p0.build();
      this.default_map.add_reg(this.PUBReservedP1_p0, `UVM_REG_ADDR_WIDTH'hFF, "RW", 0);
		this.PUBReservedP1_p0_PUBReservedP1_p0 = this.PUBReservedP1_p0.PUBReservedP1_p0;
      this.PclkGateControl = ral_reg_DWC_DDRPHYA_MASTER0_p0_PclkGateControl::type_id::create("PclkGateControl",,get_full_name());
      if(this.PclkGateControl.has_coverage(UVM_CVR_ALL))
      	this.PclkGateControl.cg_bits.option.name = {get_name(), ".", "PclkGateControl_bits"};
      this.PclkGateControl.configure(this, null, "");
      this.PclkGateControl.build();
      this.default_map.add_reg(this.PclkGateControl, `UVM_REG_ADDR_WIDTH'h200, "RW", 0);
		this.PclkGateControl_PclkEn0 = this.PclkGateControl.PclkEn0;
		this.PclkEn0 = this.PclkGateControl.PclkEn0;
		this.PclkGateControl_ReservedPclkEn0 = this.PclkGateControl.ReservedPclkEn0;
		this.ReservedPclkEn0 = this.PclkGateControl.ReservedPclkEn0;
		this.PclkGateControl_PclkEn1 = this.PclkGateControl.PclkEn1;
		this.PclkEn1 = this.PclkGateControl.PclkEn1;
		this.PclkGateControl_ReservedPclkEn1 = this.PclkGateControl.ReservedPclkEn1;
		this.ReservedPclkEn1 = this.PclkGateControl.ReservedPclkEn1;
   endfunction : build

	`uvm_object_utils(ral_block_DWC_DDRPHYA_MASTER0_p0)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_DDRPHYA_MASTER0_p0


endpackage
`endif
