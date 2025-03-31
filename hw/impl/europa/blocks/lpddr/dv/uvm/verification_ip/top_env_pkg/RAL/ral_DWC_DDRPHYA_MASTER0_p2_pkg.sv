`ifndef RAL_DWC_DDRPHYA_MASTER0_P2_PKG
`define RAL_DWC_DDRPHYA_MASTER0_P2_PKG

package ral_DWC_DDRPHYA_MASTER0_p2_pkg;
import uvm_pkg::*;

class ral_reg_DWC_DDRPHYA_MASTER0_p2_DfiFreqRatio_p2 extends uvm_reg;
	rand uvm_reg_field DfiFreqRatio_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DfiFreqRatio_p2: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p2_DfiFreqRatio_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DfiFreqRatio_p2 = uvm_reg_field::type_id::create("DfiFreqRatio_p2",,get_full_name());
      this.DfiFreqRatio_p2.configure(this, 2, 0, "RW", 0, 2'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p2_DfiFreqRatio_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p2_DfiFreqRatio_p2


class ral_reg_DWC_DDRPHYA_MASTER0_p2_PclkPtrInitVal_p2 extends uvm_reg;
	rand uvm_reg_field PclkPtrInitVal_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkPtrInitVal_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p2_PclkPtrInitVal_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkPtrInitVal_p2 = uvm_reg_field::type_id::create("PclkPtrInitVal_p2",,get_full_name());
      this.PclkPtrInitVal_p2.configure(this, 5, 0, "RW", 0, 5'h2, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p2_PclkPtrInitVal_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p2_PclkPtrInitVal_p2


class ral_reg_DWC_DDRPHYA_MASTER0_p2_CmdFifoWrModeMaster_p2 extends uvm_reg;
	rand uvm_reg_field CmdFifoWrModeMaster_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   CmdFifoWrModeMaster_p2: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_MASTER0_p2_CmdFifoWrModeMaster_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.CmdFifoWrModeMaster_p2 = uvm_reg_field::type_id::create("CmdFifoWrModeMaster_p2",,get_full_name());
      this.CmdFifoWrModeMaster_p2.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p2_CmdFifoWrModeMaster_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p2_CmdFifoWrModeMaster_p2


class ral_reg_DWC_DDRPHYA_MASTER0_p2_PipeCtl_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p2_PipeCtl_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p2_PipeCtl_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p2_PipeCtl_p2


class ral_reg_DWC_DDRPHYA_MASTER0_p2_CPclkDivRatio_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p2_CPclkDivRatio_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p2_CPclkDivRatio_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p2_CPclkDivRatio_p2


class ral_reg_DWC_DDRPHYA_MASTER0_p2_EnRxDqsTracking_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p2_EnRxDqsTracking_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p2_EnRxDqsTracking_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p2_EnRxDqsTracking_p2


class ral_reg_DWC_DDRPHYA_MASTER0_p2_DllTrainParam_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p2_DllTrainParam_p2");
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

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p2_DllTrainParam_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p2_DllTrainParam_p2


class ral_reg_DWC_DDRPHYA_MASTER0_p2_PUBReservedP1_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_MASTER0_p2_PUBReservedP1_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PUBReservedP1_p2 = uvm_reg_field::type_id::create("PUBReservedP1_p2",,get_full_name());
      this.PUBReservedP1_p2.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_MASTER0_p2_PUBReservedP1_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_MASTER0_p2_PUBReservedP1_p2


class ral_block_DWC_DDRPHYA_MASTER0_p2 extends uvm_reg_block;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p2_DfiFreqRatio_p2 DfiFreqRatio_p2;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p2_PclkPtrInitVal_p2 PclkPtrInitVal_p2;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p2_CmdFifoWrModeMaster_p2 CmdFifoWrModeMaster_p2;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p2_PipeCtl_p2 PipeCtl_p2;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p2_CPclkDivRatio_p2 CPclkDivRatio_p2;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p2_EnRxDqsTracking_p2 EnRxDqsTracking_p2;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p2_DllTrainParam_p2 DllTrainParam_p2;
	rand ral_reg_DWC_DDRPHYA_MASTER0_p2_PUBReservedP1_p2 PUBReservedP1_p2;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field DfiFreqRatio_p2_DfiFreqRatio_p2;
	rand uvm_reg_field PclkPtrInitVal_p2_PclkPtrInitVal_p2;
	rand uvm_reg_field CmdFifoWrModeMaster_p2_CmdFifoWrModeMaster_p2;
	rand uvm_reg_field PipeCtl_p2_DxInPipeEn;
	rand uvm_reg_field DxInPipeEn;
	rand uvm_reg_field PipeCtl_p2_DxOutPipeEn;
	rand uvm_reg_field DxOutPipeEn;
	rand uvm_reg_field PipeCtl_p2_AlertNPipeEn;
	rand uvm_reg_field AlertNPipeEn;
	rand uvm_reg_field PipeCtl_p2_AcInPipeEn;
	rand uvm_reg_field AcInPipeEn;
	rand uvm_reg_field CPclkDivRatio_p2_CPclkDivCa0;
	rand uvm_reg_field CPclkDivCa0;
	rand uvm_reg_field CPclkDivRatio_p2_ReservedCPclkDivCa0;
	rand uvm_reg_field ReservedCPclkDivCa0;
	rand uvm_reg_field CPclkDivRatio_p2_CPclkDivCa1;
	rand uvm_reg_field CPclkDivCa1;
	rand uvm_reg_field CPclkDivRatio_p2_ReservedCPclkDivCa1;
	rand uvm_reg_field ReservedCPclkDivCa1;
	rand uvm_reg_field CPclkDivRatio_p2_CPclkDivDq0;
	rand uvm_reg_field CPclkDivDq0;
	rand uvm_reg_field CPclkDivRatio_p2_ReservedCPclkDivDq0;
	rand uvm_reg_field ReservedCPclkDivDq0;
	rand uvm_reg_field CPclkDivRatio_p2_CPclkDivDq1;
	rand uvm_reg_field CPclkDivDq1;
	rand uvm_reg_field EnRxDqsTracking_p2_EnRxDqsTrackingPipe;
	rand uvm_reg_field EnRxDqsTrackingPipe;
	rand uvm_reg_field EnRxDqsTracking_p2_EnDqsSampNegRxEnPPT;
	rand uvm_reg_field EnDqsSampNegRxEnPPT;
	rand uvm_reg_field EnRxDqsTracking_p2_DqsSampNegRxEnSense;
	rand uvm_reg_field DqsSampNegRxEnSense;
	rand uvm_reg_field EnRxDqsTracking_p2_EnDqsSampNegRxEn;
	rand uvm_reg_field EnDqsSampNegRxEn;
	rand uvm_reg_field DllTrainParam_p2_ExtendPhdTime;
	rand uvm_reg_field ExtendPhdTime;
	rand uvm_reg_field DllTrainParam_p2_RxReplicaExtendPhdTime;
	rand uvm_reg_field RxReplicaExtendPhdTime;
	rand uvm_reg_field PUBReservedP1_p2_PUBReservedP1_p2;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	DfiFreqRatio_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h0 };
		option.weight = 1;
	}

	PclkPtrInitVal_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2 };
		option.weight = 1;
	}

	CmdFifoWrModeMaster_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3 };
		option.weight = 1;
	}

	PipeCtl_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5 };
		option.weight = 1;
	}

	CPclkDivRatio_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB };
		option.weight = 1;
	}

	EnRxDqsTracking_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h19 };
		option.weight = 1;
	}

	DllTrainParam_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h71 };
		option.weight = 1;
	}

	PUBReservedP1_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFF };
		option.weight = 1;
	}
endgroup
	function new(string name = "DWC_DDRPHYA_MASTER0_p2");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.DfiFreqRatio_p2 = ral_reg_DWC_DDRPHYA_MASTER0_p2_DfiFreqRatio_p2::type_id::create("DfiFreqRatio_p2",,get_full_name());
      if(this.DfiFreqRatio_p2.has_coverage(UVM_CVR_ALL))
      	this.DfiFreqRatio_p2.cg_bits.option.name = {get_name(), ".", "DfiFreqRatio_p2_bits"};
      this.DfiFreqRatio_p2.configure(this, null, "");
      this.DfiFreqRatio_p2.build();
      this.default_map.add_reg(this.DfiFreqRatio_p2, `UVM_REG_ADDR_WIDTH'h0, "RW", 0);
		this.DfiFreqRatio_p2_DfiFreqRatio_p2 = this.DfiFreqRatio_p2.DfiFreqRatio_p2;
      this.PclkPtrInitVal_p2 = ral_reg_DWC_DDRPHYA_MASTER0_p2_PclkPtrInitVal_p2::type_id::create("PclkPtrInitVal_p2",,get_full_name());
      if(this.PclkPtrInitVal_p2.has_coverage(UVM_CVR_ALL))
      	this.PclkPtrInitVal_p2.cg_bits.option.name = {get_name(), ".", "PclkPtrInitVal_p2_bits"};
      this.PclkPtrInitVal_p2.configure(this, null, "");
      this.PclkPtrInitVal_p2.build();
      this.default_map.add_reg(this.PclkPtrInitVal_p2, `UVM_REG_ADDR_WIDTH'h2, "RW", 0);
		this.PclkPtrInitVal_p2_PclkPtrInitVal_p2 = this.PclkPtrInitVal_p2.PclkPtrInitVal_p2;
      this.CmdFifoWrModeMaster_p2 = ral_reg_DWC_DDRPHYA_MASTER0_p2_CmdFifoWrModeMaster_p2::type_id::create("CmdFifoWrModeMaster_p2",,get_full_name());
      if(this.CmdFifoWrModeMaster_p2.has_coverage(UVM_CVR_ALL))
      	this.CmdFifoWrModeMaster_p2.cg_bits.option.name = {get_name(), ".", "CmdFifoWrModeMaster_p2_bits"};
      this.CmdFifoWrModeMaster_p2.configure(this, null, "");
      this.CmdFifoWrModeMaster_p2.build();
      this.default_map.add_reg(this.CmdFifoWrModeMaster_p2, `UVM_REG_ADDR_WIDTH'h3, "RW", 0);
		this.CmdFifoWrModeMaster_p2_CmdFifoWrModeMaster_p2 = this.CmdFifoWrModeMaster_p2.CmdFifoWrModeMaster_p2;
      this.PipeCtl_p2 = ral_reg_DWC_DDRPHYA_MASTER0_p2_PipeCtl_p2::type_id::create("PipeCtl_p2",,get_full_name());
      if(this.PipeCtl_p2.has_coverage(UVM_CVR_ALL))
      	this.PipeCtl_p2.cg_bits.option.name = {get_name(), ".", "PipeCtl_p2_bits"};
      this.PipeCtl_p2.configure(this, null, "");
      this.PipeCtl_p2.build();
      this.default_map.add_reg(this.PipeCtl_p2, `UVM_REG_ADDR_WIDTH'h5, "RW", 0);
		this.PipeCtl_p2_DxInPipeEn = this.PipeCtl_p2.DxInPipeEn;
		this.DxInPipeEn = this.PipeCtl_p2.DxInPipeEn;
		this.PipeCtl_p2_DxOutPipeEn = this.PipeCtl_p2.DxOutPipeEn;
		this.DxOutPipeEn = this.PipeCtl_p2.DxOutPipeEn;
		this.PipeCtl_p2_AlertNPipeEn = this.PipeCtl_p2.AlertNPipeEn;
		this.AlertNPipeEn = this.PipeCtl_p2.AlertNPipeEn;
		this.PipeCtl_p2_AcInPipeEn = this.PipeCtl_p2.AcInPipeEn;
		this.AcInPipeEn = this.PipeCtl_p2.AcInPipeEn;
      this.CPclkDivRatio_p2 = ral_reg_DWC_DDRPHYA_MASTER0_p2_CPclkDivRatio_p2::type_id::create("CPclkDivRatio_p2",,get_full_name());
      if(this.CPclkDivRatio_p2.has_coverage(UVM_CVR_ALL))
      	this.CPclkDivRatio_p2.cg_bits.option.name = {get_name(), ".", "CPclkDivRatio_p2_bits"};
      this.CPclkDivRatio_p2.configure(this, null, "");
      this.CPclkDivRatio_p2.build();
      this.default_map.add_reg(this.CPclkDivRatio_p2, `UVM_REG_ADDR_WIDTH'hB, "RW", 0);
		this.CPclkDivRatio_p2_CPclkDivCa0 = this.CPclkDivRatio_p2.CPclkDivCa0;
		this.CPclkDivCa0 = this.CPclkDivRatio_p2.CPclkDivCa0;
		this.CPclkDivRatio_p2_ReservedCPclkDivCa0 = this.CPclkDivRatio_p2.ReservedCPclkDivCa0;
		this.ReservedCPclkDivCa0 = this.CPclkDivRatio_p2.ReservedCPclkDivCa0;
		this.CPclkDivRatio_p2_CPclkDivCa1 = this.CPclkDivRatio_p2.CPclkDivCa1;
		this.CPclkDivCa1 = this.CPclkDivRatio_p2.CPclkDivCa1;
		this.CPclkDivRatio_p2_ReservedCPclkDivCa1 = this.CPclkDivRatio_p2.ReservedCPclkDivCa1;
		this.ReservedCPclkDivCa1 = this.CPclkDivRatio_p2.ReservedCPclkDivCa1;
		this.CPclkDivRatio_p2_CPclkDivDq0 = this.CPclkDivRatio_p2.CPclkDivDq0;
		this.CPclkDivDq0 = this.CPclkDivRatio_p2.CPclkDivDq0;
		this.CPclkDivRatio_p2_ReservedCPclkDivDq0 = this.CPclkDivRatio_p2.ReservedCPclkDivDq0;
		this.ReservedCPclkDivDq0 = this.CPclkDivRatio_p2.ReservedCPclkDivDq0;
		this.CPclkDivRatio_p2_CPclkDivDq1 = this.CPclkDivRatio_p2.CPclkDivDq1;
		this.CPclkDivDq1 = this.CPclkDivRatio_p2.CPclkDivDq1;
      this.EnRxDqsTracking_p2 = ral_reg_DWC_DDRPHYA_MASTER0_p2_EnRxDqsTracking_p2::type_id::create("EnRxDqsTracking_p2",,get_full_name());
      if(this.EnRxDqsTracking_p2.has_coverage(UVM_CVR_ALL))
      	this.EnRxDqsTracking_p2.cg_bits.option.name = {get_name(), ".", "EnRxDqsTracking_p2_bits"};
      this.EnRxDqsTracking_p2.configure(this, null, "");
      this.EnRxDqsTracking_p2.build();
      this.default_map.add_reg(this.EnRxDqsTracking_p2, `UVM_REG_ADDR_WIDTH'h19, "RW", 0);
		this.EnRxDqsTracking_p2_EnRxDqsTrackingPipe = this.EnRxDqsTracking_p2.EnRxDqsTrackingPipe;
		this.EnRxDqsTrackingPipe = this.EnRxDqsTracking_p2.EnRxDqsTrackingPipe;
		this.EnRxDqsTracking_p2_EnDqsSampNegRxEnPPT = this.EnRxDqsTracking_p2.EnDqsSampNegRxEnPPT;
		this.EnDqsSampNegRxEnPPT = this.EnRxDqsTracking_p2.EnDqsSampNegRxEnPPT;
		this.EnRxDqsTracking_p2_DqsSampNegRxEnSense = this.EnRxDqsTracking_p2.DqsSampNegRxEnSense;
		this.DqsSampNegRxEnSense = this.EnRxDqsTracking_p2.DqsSampNegRxEnSense;
		this.EnRxDqsTracking_p2_EnDqsSampNegRxEn = this.EnRxDqsTracking_p2.EnDqsSampNegRxEn;
		this.EnDqsSampNegRxEn = this.EnRxDqsTracking_p2.EnDqsSampNegRxEn;
      this.DllTrainParam_p2 = ral_reg_DWC_DDRPHYA_MASTER0_p2_DllTrainParam_p2::type_id::create("DllTrainParam_p2",,get_full_name());
      if(this.DllTrainParam_p2.has_coverage(UVM_CVR_ALL))
      	this.DllTrainParam_p2.cg_bits.option.name = {get_name(), ".", "DllTrainParam_p2_bits"};
      this.DllTrainParam_p2.configure(this, null, "");
      this.DllTrainParam_p2.build();
      this.default_map.add_reg(this.DllTrainParam_p2, `UVM_REG_ADDR_WIDTH'h71, "RW", 0);
		this.DllTrainParam_p2_ExtendPhdTime = this.DllTrainParam_p2.ExtendPhdTime;
		this.ExtendPhdTime = this.DllTrainParam_p2.ExtendPhdTime;
		this.DllTrainParam_p2_RxReplicaExtendPhdTime = this.DllTrainParam_p2.RxReplicaExtendPhdTime;
		this.RxReplicaExtendPhdTime = this.DllTrainParam_p2.RxReplicaExtendPhdTime;
      this.PUBReservedP1_p2 = ral_reg_DWC_DDRPHYA_MASTER0_p2_PUBReservedP1_p2::type_id::create("PUBReservedP1_p2",,get_full_name());
      if(this.PUBReservedP1_p2.has_coverage(UVM_CVR_ALL))
      	this.PUBReservedP1_p2.cg_bits.option.name = {get_name(), ".", "PUBReservedP1_p2_bits"};
      this.PUBReservedP1_p2.configure(this, null, "");
      this.PUBReservedP1_p2.build();
      this.default_map.add_reg(this.PUBReservedP1_p2, `UVM_REG_ADDR_WIDTH'hFF, "RW", 0);
		this.PUBReservedP1_p2_PUBReservedP1_p2 = this.PUBReservedP1_p2.PUBReservedP1_p2;
   endfunction : build

	`uvm_object_utils(ral_block_DWC_DDRPHYA_MASTER0_p2)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_DDRPHYA_MASTER0_p2


endpackage
`endif
