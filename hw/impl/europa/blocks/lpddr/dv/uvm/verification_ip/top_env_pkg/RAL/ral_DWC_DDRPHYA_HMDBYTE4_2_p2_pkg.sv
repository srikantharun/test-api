`ifndef RAL_DWC_DDRPHYA_HMDBYTE4_2_P2_PKG
`define RAL_DWC_DDRPHYA_HMDBYTE4_2_P2_PKG

package ral_DWC_DDRPHYA_HMDBYTE4_2_p2_pkg;
import uvm_pkg::*;

class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFECtrlDq_p2 extends uvm_reg;
	rand uvm_reg_field RxDFECtrlDq_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFECtrlDq_p2: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFECtrlDq_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFECtrlDq_p2 = uvm_reg_field::type_id::create("RxDFECtrlDq_p2",,get_full_name());
      this.RxDFECtrlDq_p2.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFECtrlDq_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFECtrlDq_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_LpDqPowerDnDly_p2 extends uvm_reg;
	rand uvm_reg_field LpDqPowerDnDly_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   LpDqPowerDnDly_p2: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_LpDqPowerDnDly_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.LpDqPowerDnDly_p2 = uvm_reg_field::type_id::create("LpDqPowerDnDly_p2",,get_full_name());
      this.LpDqPowerDnDly_p2.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_LpDqPowerDnDly_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_LpDqPowerDnDly_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_DxDigStrobeMode_p2 extends uvm_reg;
	rand uvm_reg_field DxDigStrobeMode_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DxDigStrobeMode_p2: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_DxDigStrobeMode_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DxDigStrobeMode_p2 = uvm_reg_field::type_id::create("DxDigStrobeMode_p2",,get_full_name());
      this.DxDigStrobeMode_p2.configure(this, 2, 0, "RW", 0, 2'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_DxDigStrobeMode_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_DxDigStrobeMode_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_DqVregRsvdP_p2 extends uvm_reg;
	rand uvm_reg_field DqVregRsvdP_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   DqVregRsvdP_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_DqVregRsvdP_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.DqVregRsvdP_p2 = uvm_reg_field::type_id::create("DqVregRsvdP_p2",,get_full_name());
      this.DqVregRsvdP_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_DqVregRsvdP_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_DqVregRsvdP_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_EnaRxStrobeEnB_p2 extends uvm_reg;
	rand uvm_reg_field EnaRxStrobeEnB_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   EnaRxStrobeEnB_p2: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_EnaRxStrobeEnB_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.EnaRxStrobeEnB_p2 = uvm_reg_field::type_id::create("EnaRxStrobeEnB_p2",,get_full_name());
      this.EnaRxStrobeEnB_p2.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_EnaRxStrobeEnB_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_EnaRxStrobeEnB_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDQSlew_p2 extends uvm_reg;
	rand uvm_reg_field TxDQSlewPU;
	rand uvm_reg_field TxDQSlewPD;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDQSlewPU: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   TxDQSlewPD: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_TxDQSlew_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDQSlewPU = uvm_reg_field::type_id::create("TxDQSlewPU",,get_full_name());
      this.TxDQSlewPU.configure(this, 4, 0, "RW", 0, 4'h1, 1, 0, 0);
      this.TxDQSlewPD = uvm_reg_field::type_id::create("TxDQSlewPD",,get_full_name());
      this.TxDQSlewPD.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDQSlew_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDQSlew_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxImpedanceDq_p2 extends uvm_reg;
	rand uvm_reg_field TxStrenCodeDqPU;
	rand uvm_reg_field TxStrenCodeDqPD;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxStrenCodeDqPU: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   TxStrenCodeDqPD: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_TxImpedanceDq_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxStrenCodeDqPU = uvm_reg_field::type_id::create("TxStrenCodeDqPU",,get_full_name());
      this.TxStrenCodeDqPU.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.TxStrenCodeDqPD = uvm_reg_field::type_id::create("TxStrenCodeDqPD",,get_full_name());
      this.TxStrenCodeDqPD.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxImpedanceDq_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxImpedanceDq_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxImpedanceDqs_p2 extends uvm_reg;
	rand uvm_reg_field TxStrenCodeDqsPUT;
	rand uvm_reg_field TxStrenCodeDqsPUC;
	rand uvm_reg_field TxStrenCodeDqsPDT;
	rand uvm_reg_field TxStrenCodeDqsPDC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxStrenCodeDqsPUT: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   TxStrenCodeDqsPUC: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   TxStrenCodeDqsPDT: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   TxStrenCodeDqsPDC: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_TxImpedanceDqs_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxStrenCodeDqsPUT = uvm_reg_field::type_id::create("TxStrenCodeDqsPUT",,get_full_name());
      this.TxStrenCodeDqsPUT.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.TxStrenCodeDqsPUC = uvm_reg_field::type_id::create("TxStrenCodeDqsPUC",,get_full_name());
      this.TxStrenCodeDqsPUC.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.TxStrenCodeDqsPDT = uvm_reg_field::type_id::create("TxStrenCodeDqsPDT",,get_full_name());
      this.TxStrenCodeDqsPDT.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.TxStrenCodeDqsPDC = uvm_reg_field::type_id::create("TxStrenCodeDqsPDC",,get_full_name());
      this.TxStrenCodeDqsPDC.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxImpedanceDqs_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxImpedanceDqs_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_OdtImpedanceDq_p2 extends uvm_reg;
	rand uvm_reg_field OdtStrenCodeDqPU;
	rand uvm_reg_field OdtStrenCodeDqPD;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   OdtStrenCodeDqPU: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   OdtStrenCodeDqPD: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_OdtImpedanceDq_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.OdtStrenCodeDqPU = uvm_reg_field::type_id::create("OdtStrenCodeDqPU",,get_full_name());
      this.OdtStrenCodeDqPU.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.OdtStrenCodeDqPD = uvm_reg_field::type_id::create("OdtStrenCodeDqPD",,get_full_name());
      this.OdtStrenCodeDqPD.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_OdtImpedanceDq_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_OdtImpedanceDq_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_OdtImpedanceDqs_p2 extends uvm_reg;
	rand uvm_reg_field OdtStrenCodeDqsPUT;
	rand uvm_reg_field OdtStrenCodeDqsPUC;
	rand uvm_reg_field OdtStrenCodeDqsPDT;
	rand uvm_reg_field OdtStrenCodeDqsPDC;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   OdtStrenCodeDqsPUT: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   OdtStrenCodeDqsPUC: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   OdtStrenCodeDqsPDT: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   OdtStrenCodeDqsPDC: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_OdtImpedanceDqs_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.OdtStrenCodeDqsPUT = uvm_reg_field::type_id::create("OdtStrenCodeDqsPUT",,get_full_name());
      this.OdtStrenCodeDqsPUT.configure(this, 4, 0, "RW", 0, 4'h0, 1, 0, 0);
      this.OdtStrenCodeDqsPUC = uvm_reg_field::type_id::create("OdtStrenCodeDqsPUC",,get_full_name());
      this.OdtStrenCodeDqsPUC.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
      this.OdtStrenCodeDqsPDT = uvm_reg_field::type_id::create("OdtStrenCodeDqsPDT",,get_full_name());
      this.OdtStrenCodeDqsPDT.configure(this, 4, 8, "RW", 0, 4'h0, 1, 0, 0);
      this.OdtStrenCodeDqsPDC = uvm_reg_field::type_id::create("OdtStrenCodeDqsPDC",,get_full_name());
      this.OdtStrenCodeDqsPDC.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_OdtImpedanceDqs_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_OdtImpedanceDqs_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDQSSeVrefDAC0_p2 extends uvm_reg;
	rand uvm_reg_field RxDQSSeVrefDAC0_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDQSSeVrefDAC0_p2: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDQSSeVrefDAC0_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDQSSeVrefDAC0_p2 = uvm_reg_field::type_id::create("RxDQSSeVrefDAC0_p2",,get_full_name());
      this.RxDQSSeVrefDAC0_p2.configure(this, 9, 0, "RW", 0, 9'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDQSSeVrefDAC0_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDQSSeVrefDAC0_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDQSCtrl_p2 extends uvm_reg;
	rand uvm_reg_field RxDQSDiffSeVrefDACEn;
	rand uvm_reg_field RxDiffSeCtrl;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDQSDiffSeVrefDACEn: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   RxDiffSeCtrl: coverpoint {m_data[2:1], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDQSCtrl_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDQSDiffSeVrefDACEn = uvm_reg_field::type_id::create("RxDQSDiffSeVrefDACEn",,get_full_name());
      this.RxDQSDiffSeVrefDACEn.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.RxDiffSeCtrl = uvm_reg_field::type_id::create("RxDiffSeCtrl",,get_full_name());
      this.RxDiffSeCtrl.configure(this, 2, 1, "RW", 0, 2'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDQSCtrl_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDQSCtrl_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDQDcaMode_p2 extends uvm_reg;
	rand uvm_reg_field TxDQDcaMode_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDQDcaMode_p2: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_TxDQDcaMode_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDQDcaMode_p2 = uvm_reg_field::type_id::create("TxDQDcaMode_p2",,get_full_name());
      this.TxDQDcaMode_p2.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDQDcaMode_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDQDcaMode_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMTxLcdlSeed_p2 extends uvm_reg;
	rand uvm_reg_field HMTxLcdlSeed_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HMTxLcdlSeed_p2: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_HMTxLcdlSeed_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMTxLcdlSeed_p2 = uvm_reg_field::type_id::create("HMTxLcdlSeed_p2",,get_full_name());
      this.HMTxLcdlSeed_p2.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMTxLcdlSeed_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMTxLcdlSeed_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMRxLcdlSeed_p2 extends uvm_reg;
	rand uvm_reg_field HMRxLcdlSeed_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HMRxLcdlSeed_p2: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_HMRxLcdlSeed_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMRxLcdlSeed_p2 = uvm_reg_field::type_id::create("HMRxLcdlSeed_p2",,get_full_name());
      this.HMRxLcdlSeed_p2.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMRxLcdlSeed_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMRxLcdlSeed_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_LcdlMonitorCtl_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_LcdlMonitorCtl_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.StickyUnlckThrshld = uvm_reg_field::type_id::create("StickyUnlckThrshld",,get_full_name());
      this.StickyUnlckThrshld.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_LcdlMonitorCtl_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_LcdlMonitorCtl_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMDBYTELcdlCalDeltaMM_p2 extends uvm_reg;
	rand uvm_reg_field TxLcdlCalDeltaMM;
	rand uvm_reg_field RxLcdlCalDeltaMM;
	rand uvm_reg_field RxReplicaLcdlCalDeltaMM;
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
	   RxLcdlCalDeltaMM: coverpoint {m_data[9:5], m_is_read} iff(m_be) {
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
	   RxReplicaLcdlCalDeltaMM: coverpoint {m_data[14:10], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_HMDBYTELcdlCalDeltaMM_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxLcdlCalDeltaMM = uvm_reg_field::type_id::create("TxLcdlCalDeltaMM",,get_full_name());
      this.TxLcdlCalDeltaMM.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 0);
      this.RxLcdlCalDeltaMM = uvm_reg_field::type_id::create("RxLcdlCalDeltaMM",,get_full_name());
      this.RxLcdlCalDeltaMM.configure(this, 5, 5, "RW", 0, 5'h0, 1, 0, 0);
      this.RxReplicaLcdlCalDeltaMM = uvm_reg_field::type_id::create("RxReplicaLcdlCalDeltaMM",,get_full_name());
      this.RxReplicaLcdlCalDeltaMM.configure(this, 5, 10, "RW", 0, 5'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMDBYTELcdlCalDeltaMM_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMDBYTELcdlCalDeltaMM_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn0_p2 extends uvm_reg;
	rand uvm_reg_field RxOffsetSelEvenSLn0_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxOffsetSelEvenSLn0_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn0_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxOffsetSelEvenSLn0_p2 = uvm_reg_field::type_id::create("RxOffsetSelEvenSLn0_p2",,get_full_name());
      this.RxOffsetSelEvenSLn0_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn0_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn0_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn1_p2 extends uvm_reg;
	rand uvm_reg_field RxOffsetSelEvenSLn1_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxOffsetSelEvenSLn1_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn1_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxOffsetSelEvenSLn1_p2 = uvm_reg_field::type_id::create("RxOffsetSelEvenSLn1_p2",,get_full_name());
      this.RxOffsetSelEvenSLn1_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn1_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn1_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn2_p2 extends uvm_reg;
	rand uvm_reg_field RxOffsetSelEvenSLn2_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxOffsetSelEvenSLn2_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn2_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxOffsetSelEvenSLn2_p2 = uvm_reg_field::type_id::create("RxOffsetSelEvenSLn2_p2",,get_full_name());
      this.RxOffsetSelEvenSLn2_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn2_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn2_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn3_p2 extends uvm_reg;
	rand uvm_reg_field RxOffsetSelEvenSLn3_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxOffsetSelEvenSLn3_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn3_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxOffsetSelEvenSLn3_p2 = uvm_reg_field::type_id::create("RxOffsetSelEvenSLn3_p2",,get_full_name());
      this.RxOffsetSelEvenSLn3_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn3_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn3_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn0_p2 extends uvm_reg;
	rand uvm_reg_field RxOffsetSelOddSLn0_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxOffsetSelOddSLn0_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn0_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxOffsetSelOddSLn0_p2 = uvm_reg_field::type_id::create("RxOffsetSelOddSLn0_p2",,get_full_name());
      this.RxOffsetSelOddSLn0_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn0_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn0_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn1_p2 extends uvm_reg;
	rand uvm_reg_field RxOffsetSelOddSLn1_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxOffsetSelOddSLn1_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn1_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxOffsetSelOddSLn1_p2 = uvm_reg_field::type_id::create("RxOffsetSelOddSLn1_p2",,get_full_name());
      this.RxOffsetSelOddSLn1_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn1_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn1_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn2_p2 extends uvm_reg;
	rand uvm_reg_field RxOffsetSelOddSLn2_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxOffsetSelOddSLn2_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn2_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxOffsetSelOddSLn2_p2 = uvm_reg_field::type_id::create("RxOffsetSelOddSLn2_p2",,get_full_name());
      this.RxOffsetSelOddSLn2_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn2_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn2_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn3_p2 extends uvm_reg;
	rand uvm_reg_field RxOffsetSelOddSLn3_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxOffsetSelOddSLn3_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn3_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxOffsetSelOddSLn3_p2 = uvm_reg_field::type_id::create("RxOffsetSelOddSLn3_p2",,get_full_name());
      this.RxOffsetSelOddSLn3_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn3_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn3_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMRxReplicaLcdlSeed_p2 extends uvm_reg;
	rand uvm_reg_field HMRxReplicaLcdlSeed_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HMRxReplicaLcdlSeed_p2: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_HMRxReplicaLcdlSeed_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMRxReplicaLcdlSeed_p2 = uvm_reg_field::type_id::create("HMRxReplicaLcdlSeed_p2",,get_full_name());
      this.HMRxReplicaLcdlSeed_p2.configure(this, 16, 0, "RW", 0, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMRxReplicaLcdlSeed_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMRxReplicaLcdlSeed_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDiffDcaMode_p2 extends uvm_reg;
	rand uvm_reg_field TxDiffDcaMode_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDiffDcaMode_p2: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_TxDiffDcaMode_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDiffDcaMode_p2 = uvm_reg_field::type_id::create("TxDiffDcaMode_p2",,get_full_name());
      this.TxDiffDcaMode_p2.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDiffDcaMode_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDiffDcaMode_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln0_p2 extends uvm_reg;
	rand uvm_reg_field RxDFETap1SelTg0Ln0_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap1SelTg0Ln0_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln0_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap1SelTg0Ln0_p2 = uvm_reg_field::type_id::create("RxDFETap1SelTg0Ln0_p2",,get_full_name());
      this.RxDFETap1SelTg0Ln0_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln0_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln0_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln0_p2 extends uvm_reg;
	rand uvm_reg_field RxDFETap1SelTg1Ln0_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap1SelTg1Ln0_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln0_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap1SelTg1Ln0_p2 = uvm_reg_field::type_id::create("RxDFETap1SelTg1Ln0_p2",,get_full_name());
      this.RxDFETap1SelTg1Ln0_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln0_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln0_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln0_p2 extends uvm_reg;
	rand uvm_reg_field RxDFETap2SelTg0Ln0_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap2SelTg0Ln0_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln0_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap2SelTg0Ln0_p2 = uvm_reg_field::type_id::create("RxDFETap2SelTg0Ln0_p2",,get_full_name());
      this.RxDFETap2SelTg0Ln0_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln0_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln0_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln0_p2 extends uvm_reg;
	rand uvm_reg_field RxDFETap2SelTg1Ln0_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap2SelTg1Ln0_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln0_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap2SelTg1Ln0_p2 = uvm_reg_field::type_id::create("RxDFETap2SelTg1Ln0_p2",,get_full_name());
      this.RxDFETap2SelTg1Ln0_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln0_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln0_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln1_p2 extends uvm_reg;
	rand uvm_reg_field RxDFETap1SelTg0Ln1_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap1SelTg0Ln1_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln1_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap1SelTg0Ln1_p2 = uvm_reg_field::type_id::create("RxDFETap1SelTg0Ln1_p2",,get_full_name());
      this.RxDFETap1SelTg0Ln1_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln1_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln1_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln1_p2 extends uvm_reg;
	rand uvm_reg_field RxDFETap1SelTg1Ln1_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap1SelTg1Ln1_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln1_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap1SelTg1Ln1_p2 = uvm_reg_field::type_id::create("RxDFETap1SelTg1Ln1_p2",,get_full_name());
      this.RxDFETap1SelTg1Ln1_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln1_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln1_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln1_p2 extends uvm_reg;
	rand uvm_reg_field RxDFETap2SelTg0Ln1_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap2SelTg0Ln1_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln1_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap2SelTg0Ln1_p2 = uvm_reg_field::type_id::create("RxDFETap2SelTg0Ln1_p2",,get_full_name());
      this.RxDFETap2SelTg0Ln1_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln1_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln1_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln1_p2 extends uvm_reg;
	rand uvm_reg_field RxDFETap2SelTg1Ln1_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap2SelTg1Ln1_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln1_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap2SelTg1Ln1_p2 = uvm_reg_field::type_id::create("RxDFETap2SelTg1Ln1_p2",,get_full_name());
      this.RxDFETap2SelTg1Ln1_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln1_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln1_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln2_p2 extends uvm_reg;
	rand uvm_reg_field RxDFETap1SelTg0Ln2_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap1SelTg0Ln2_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln2_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap1SelTg0Ln2_p2 = uvm_reg_field::type_id::create("RxDFETap1SelTg0Ln2_p2",,get_full_name());
      this.RxDFETap1SelTg0Ln2_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln2_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln2_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln2_p2 extends uvm_reg;
	rand uvm_reg_field RxDFETap1SelTg1Ln2_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap1SelTg1Ln2_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln2_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap1SelTg1Ln2_p2 = uvm_reg_field::type_id::create("RxDFETap1SelTg1Ln2_p2",,get_full_name());
      this.RxDFETap1SelTg1Ln2_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln2_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln2_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln2_p2 extends uvm_reg;
	rand uvm_reg_field RxDFETap2SelTg0Ln2_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap2SelTg0Ln2_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln2_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap2SelTg0Ln2_p2 = uvm_reg_field::type_id::create("RxDFETap2SelTg0Ln2_p2",,get_full_name());
      this.RxDFETap2SelTg0Ln2_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln2_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln2_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln2_p2 extends uvm_reg;
	rand uvm_reg_field RxDFETap2SelTg1Ln2_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap2SelTg1Ln2_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln2_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap2SelTg1Ln2_p2 = uvm_reg_field::type_id::create("RxDFETap2SelTg1Ln2_p2",,get_full_name());
      this.RxDFETap2SelTg1Ln2_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln2_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln2_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln3_p2 extends uvm_reg;
	rand uvm_reg_field RxDFETap1SelTg0Ln3_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap1SelTg0Ln3_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln3_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap1SelTg0Ln3_p2 = uvm_reg_field::type_id::create("RxDFETap1SelTg0Ln3_p2",,get_full_name());
      this.RxDFETap1SelTg0Ln3_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln3_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln3_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln3_p2 extends uvm_reg;
	rand uvm_reg_field RxDFETap1SelTg1Ln3_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap1SelTg1Ln3_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln3_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap1SelTg1Ln3_p2 = uvm_reg_field::type_id::create("RxDFETap1SelTg1Ln3_p2",,get_full_name());
      this.RxDFETap1SelTg1Ln3_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln3_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln3_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln3_p2 extends uvm_reg;
	rand uvm_reg_field RxDFETap2SelTg0Ln3_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap2SelTg0Ln3_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln3_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap2SelTg0Ln3_p2 = uvm_reg_field::type_id::create("RxDFETap2SelTg0Ln3_p2",,get_full_name());
      this.RxDFETap2SelTg0Ln3_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln3_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln3_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln3_p2 extends uvm_reg;
	rand uvm_reg_field RxDFETap2SelTg1Ln3_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDFETap2SelTg1Ln3_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln3_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDFETap2SelTg1Ln3_p2 = uvm_reg_field::type_id::create("RxDFETap2SelTg1Ln3_p2",,get_full_name());
      this.RxDFETap2SelTg1Ln3_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln3_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln3_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn0_p2 extends uvm_reg;
	rand uvm_reg_field PclkDCACoarseDqLn0;
	rand uvm_reg_field PclkDCAFineDqLn0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACoarseDqLn0: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	   PclkDCAFineDqLn0: coverpoint {m_data[8:5], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn0_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACoarseDqLn0 = uvm_reg_field::type_id::create("PclkDCACoarseDqLn0",,get_full_name());
      this.PclkDCACoarseDqLn0.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 0);
      this.PclkDCAFineDqLn0 = uvm_reg_field::type_id::create("PclkDCAFineDqLn0",,get_full_name());
      this.PclkDCAFineDqLn0.configure(this, 4, 5, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn0_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn0_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn1_p2 extends uvm_reg;
	rand uvm_reg_field PclkDCACoarseDqLn1;
	rand uvm_reg_field PclkDCAFineDqLn1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACoarseDqLn1: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	   PclkDCAFineDqLn1: coverpoint {m_data[8:5], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn1_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACoarseDqLn1 = uvm_reg_field::type_id::create("PclkDCACoarseDqLn1",,get_full_name());
      this.PclkDCACoarseDqLn1.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 0);
      this.PclkDCAFineDqLn1 = uvm_reg_field::type_id::create("PclkDCAFineDqLn1",,get_full_name());
      this.PclkDCAFineDqLn1.configure(this, 4, 5, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn1_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn1_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn2_p2 extends uvm_reg;
	rand uvm_reg_field PclkDCACoarseDqLn2;
	rand uvm_reg_field PclkDCAFineDqLn2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACoarseDqLn2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	   PclkDCAFineDqLn2: coverpoint {m_data[8:5], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn2_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACoarseDqLn2 = uvm_reg_field::type_id::create("PclkDCACoarseDqLn2",,get_full_name());
      this.PclkDCACoarseDqLn2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 0);
      this.PclkDCAFineDqLn2 = uvm_reg_field::type_id::create("PclkDCAFineDqLn2",,get_full_name());
      this.PclkDCAFineDqLn2.configure(this, 4, 5, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn2_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn2_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn3_p2 extends uvm_reg;
	rand uvm_reg_field PclkDCACoarseDqLn3;
	rand uvm_reg_field PclkDCAFineDqLn3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACoarseDqLn3: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	   PclkDCAFineDqLn3: coverpoint {m_data[8:5], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn3_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACoarseDqLn3 = uvm_reg_field::type_id::create("PclkDCACoarseDqLn3",,get_full_name());
      this.PclkDCACoarseDqLn3.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 0);
      this.PclkDCAFineDqLn3 = uvm_reg_field::type_id::create("PclkDCAFineDqLn3",,get_full_name());
      this.PclkDCAFineDqLn3.configure(this, 4, 5, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn3_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn3_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDQS_p2 extends uvm_reg;
	rand uvm_reg_field PclkDCACoarseDQS;
	rand uvm_reg_field PclkDCAFineDQS;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCACoarseDQS: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	   PclkDCAFineDQS: coverpoint {m_data[8:5], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDQS_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCACoarseDQS = uvm_reg_field::type_id::create("PclkDCACoarseDQS",,get_full_name());
      this.PclkDCACoarseDQS.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 0);
      this.PclkDCAFineDQS = uvm_reg_field::type_id::create("PclkDCAFineDQS",,get_full_name());
      this.PclkDCAFineDQS.configure(this, 4, 5, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDQS_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDQS_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMReservedP1_p2 extends uvm_reg;
	rand uvm_reg_field HMReservedP1_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   HMReservedP1_p2: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_HMReservedP1_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.HMReservedP1_p2 = uvm_reg_field::type_id::create("HMReservedP1_p2",,get_full_name());
      this.HMReservedP1_p2.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMReservedP1_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMReservedP1_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCATxLcdlPhase_p2 extends uvm_reg;
	rand uvm_reg_field PclkDCATxLcdlPhase_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCATxLcdlPhase_p2: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCATxLcdlPhase_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCATxLcdlPhase_p2 = uvm_reg_field::type_id::create("PclkDCATxLcdlPhase_p2",,get_full_name());
      this.PclkDCATxLcdlPhase_p2.configure(this, 7, 0, "RW", 0, 7'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCATxLcdlPhase_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCATxLcdlPhase_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn0_p2 extends uvm_reg;
	rand uvm_reg_field PclkDCDOffsetDqLn0_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCDOffsetDqLn0_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn0_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCDOffsetDqLn0_p2 = uvm_reg_field::type_id::create("PclkDCDOffsetDqLn0_p2",,get_full_name());
      this.PclkDCDOffsetDqLn0_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn0_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn0_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn1_p2 extends uvm_reg;
	rand uvm_reg_field PclkDCDOffsetDqLn1_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCDOffsetDqLn1_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn1_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCDOffsetDqLn1_p2 = uvm_reg_field::type_id::create("PclkDCDOffsetDqLn1_p2",,get_full_name());
      this.PclkDCDOffsetDqLn1_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn1_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn1_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn2_p2 extends uvm_reg;
	rand uvm_reg_field PclkDCDOffsetDqLn2_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCDOffsetDqLn2_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn2_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCDOffsetDqLn2_p2 = uvm_reg_field::type_id::create("PclkDCDOffsetDqLn2_p2",,get_full_name());
      this.PclkDCDOffsetDqLn2_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn2_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn2_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn3_p2 extends uvm_reg;
	rand uvm_reg_field PclkDCDOffsetDqLn3_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCDOffsetDqLn3_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn3_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCDOffsetDqLn3_p2 = uvm_reg_field::type_id::create("PclkDCDOffsetDqLn3_p2",,get_full_name());
      this.PclkDCDOffsetDqLn3_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn3_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn3_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDQS_p2 extends uvm_reg;
	rand uvm_reg_field PclkDCDOffsetDQS_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCDOffsetDQS_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDQS_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCDOffsetDQS_p2 = uvm_reg_field::type_id::create("PclkDCDOffsetDQS_p2",,get_full_name());
      this.PclkDCDOffsetDQS_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDQS_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDQS_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTTg0_p2 extends uvm_reg;
	rand uvm_reg_field TxDcaFinePDTTg0;
	rand uvm_reg_field TxDcaFinePUTTg0;
	rand uvm_reg_field TxDcaCoarseTTg0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaFinePDTTg0: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUTTg0: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   TxDcaCoarseTTg0: coverpoint {m_data[9:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTTg0_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaFinePDTTg0 = uvm_reg_field::type_id::create("TxDcaFinePDTTg0",,get_full_name());
      this.TxDcaFinePDTTg0.configure(this, 4, 0, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePUTTg0 = uvm_reg_field::type_id::create("TxDcaFinePUTTg0",,get_full_name());
      this.TxDcaFinePUTTg0.configure(this, 4, 4, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaCoarseTTg0 = uvm_reg_field::type_id::create("TxDcaCoarseTTg0",,get_full_name());
      this.TxDcaCoarseTTg0.configure(this, 2, 8, "RW", 0, 2'h3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTTg0_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTTg0_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTTg1_p2 extends uvm_reg;
	rand uvm_reg_field TxDcaFinePDTTg1;
	rand uvm_reg_field TxDcaFinePUTTg1;
	rand uvm_reg_field TxDcaCoarseTTg1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaFinePDTTg1: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUTTg1: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   TxDcaCoarseTTg1: coverpoint {m_data[9:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTTg1_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaFinePDTTg1 = uvm_reg_field::type_id::create("TxDcaFinePDTTg1",,get_full_name());
      this.TxDcaFinePDTTg1.configure(this, 4, 0, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePUTTg1 = uvm_reg_field::type_id::create("TxDcaFinePUTTg1",,get_full_name());
      this.TxDcaFinePUTTg1.configure(this, 4, 4, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaCoarseTTg1 = uvm_reg_field::type_id::create("TxDcaCoarseTTg1",,get_full_name());
      this.TxDcaCoarseTTg1.configure(this, 2, 8, "RW", 0, 2'h3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTTg1_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTTg1_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlCTg0_p2 extends uvm_reg;
	rand uvm_reg_field TxDcaFinePDCTg0;
	rand uvm_reg_field TxDcaFinePUCTg0;
	rand uvm_reg_field TxDcaCoarseCTg0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaFinePDCTg0: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUCTg0: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   TxDcaCoarseCTg0: coverpoint {m_data[9:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlCTg0_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaFinePDCTg0 = uvm_reg_field::type_id::create("TxDcaFinePDCTg0",,get_full_name());
      this.TxDcaFinePDCTg0.configure(this, 4, 0, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePUCTg0 = uvm_reg_field::type_id::create("TxDcaFinePUCTg0",,get_full_name());
      this.TxDcaFinePUCTg0.configure(this, 4, 4, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaCoarseCTg0 = uvm_reg_field::type_id::create("TxDcaCoarseCTg0",,get_full_name());
      this.TxDcaCoarseCTg0.configure(this, 2, 8, "RW", 0, 2'h3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlCTg0_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlCTg0_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlCTg1_p2 extends uvm_reg;
	rand uvm_reg_field TxDcaFinePDCTg1;
	rand uvm_reg_field TxDcaFinePUCTg1;
	rand uvm_reg_field TxDcaCoarseCTg1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaFinePDCTg1: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUCTg1: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   TxDcaCoarseCTg1: coverpoint {m_data[9:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlCTg1_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaFinePDCTg1 = uvm_reg_field::type_id::create("TxDcaFinePDCTg1",,get_full_name());
      this.TxDcaFinePDCTg1.configure(this, 4, 0, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePUCTg1 = uvm_reg_field::type_id::create("TxDcaFinePUCTg1",,get_full_name());
      this.TxDcaFinePUCTg1.configure(this, 4, 4, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaCoarseCTg1 = uvm_reg_field::type_id::create("TxDcaCoarseCTg1",,get_full_name());
      this.TxDcaCoarseCTg1.configure(this, 2, 8, "RW", 0, 2'h3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlCTg1_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlCTg1_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlTTg0_p2 extends uvm_reg;
	rand uvm_reg_field RxDcaFinePDTTg0;
	rand uvm_reg_field RxDcaFinePUTTg0;
	rand uvm_reg_field RxDcaCoarseTTg0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDcaFinePDTTg0: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   RxDcaFinePUTTg0: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   RxDcaCoarseTTg0: coverpoint {m_data[9:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlTTg0_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDcaFinePDTTg0 = uvm_reg_field::type_id::create("RxDcaFinePDTTg0",,get_full_name());
      this.RxDcaFinePDTTg0.configure(this, 4, 0, "RW", 0, 4'h6, 1, 0, 0);
      this.RxDcaFinePUTTg0 = uvm_reg_field::type_id::create("RxDcaFinePUTTg0",,get_full_name());
      this.RxDcaFinePUTTg0.configure(this, 4, 4, "RW", 0, 4'h6, 1, 0, 0);
      this.RxDcaCoarseTTg0 = uvm_reg_field::type_id::create("RxDcaCoarseTTg0",,get_full_name());
      this.RxDcaCoarseTTg0.configure(this, 2, 8, "RW", 0, 2'h3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlTTg0_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlTTg0_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlTTg1_p2 extends uvm_reg;
	rand uvm_reg_field RxDcaFinePDTTg1;
	rand uvm_reg_field RxDcaFinePUTTg1;
	rand uvm_reg_field RxDcaCoarseTTg1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDcaFinePDTTg1: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   RxDcaFinePUTTg1: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   RxDcaCoarseTTg1: coverpoint {m_data[9:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlTTg1_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDcaFinePDTTg1 = uvm_reg_field::type_id::create("RxDcaFinePDTTg1",,get_full_name());
      this.RxDcaFinePDTTg1.configure(this, 4, 0, "RW", 0, 4'h6, 1, 0, 0);
      this.RxDcaFinePUTTg1 = uvm_reg_field::type_id::create("RxDcaFinePUTTg1",,get_full_name());
      this.RxDcaFinePUTTg1.configure(this, 4, 4, "RW", 0, 4'h6, 1, 0, 0);
      this.RxDcaCoarseTTg1 = uvm_reg_field::type_id::create("RxDcaCoarseTTg1",,get_full_name());
      this.RxDcaCoarseTTg1.configure(this, 2, 8, "RW", 0, 2'h3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlTTg1_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlTTg1_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlCTg0_p2 extends uvm_reg;
	rand uvm_reg_field RxDcaFinePDCTg0;
	rand uvm_reg_field RxDcaFinePUCTg0;
	rand uvm_reg_field RxDcaCoarseCTg0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDcaFinePDCTg0: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   RxDcaFinePUCTg0: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   RxDcaCoarseCTg0: coverpoint {m_data[9:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlCTg0_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDcaFinePDCTg0 = uvm_reg_field::type_id::create("RxDcaFinePDCTg0",,get_full_name());
      this.RxDcaFinePDCTg0.configure(this, 4, 0, "RW", 0, 4'h6, 1, 0, 0);
      this.RxDcaFinePUCTg0 = uvm_reg_field::type_id::create("RxDcaFinePUCTg0",,get_full_name());
      this.RxDcaFinePUCTg0.configure(this, 4, 4, "RW", 0, 4'h6, 1, 0, 0);
      this.RxDcaCoarseCTg0 = uvm_reg_field::type_id::create("RxDcaCoarseCTg0",,get_full_name());
      this.RxDcaCoarseCTg0.configure(this, 2, 8, "RW", 0, 2'h3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlCTg0_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlCTg0_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlCTg1_p2 extends uvm_reg;
	rand uvm_reg_field RxDcaFinePDCTg1;
	rand uvm_reg_field RxDcaFinePUCTg1;
	rand uvm_reg_field RxDcaCoarseCTg1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   RxDcaFinePDCTg1: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   RxDcaFinePUCTg1: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	   RxDcaCoarseCTg1: coverpoint {m_data[9:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlCTg1_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.RxDcaFinePDCTg1 = uvm_reg_field::type_id::create("RxDcaFinePDCTg1",,get_full_name());
      this.RxDcaFinePDCTg1.configure(this, 4, 0, "RW", 0, 4'h6, 1, 0, 0);
      this.RxDcaFinePUCTg1 = uvm_reg_field::type_id::create("RxDcaFinePUCTg1",,get_full_name());
      this.RxDcaFinePUCTg1.configure(this, 4, 4, "RW", 0, 4'h6, 1, 0, 0);
      this.RxDcaCoarseCTg1 = uvm_reg_field::type_id::create("RxDcaCoarseCTg1",,get_full_name());
      this.RxDcaCoarseCTg1.configure(this, 2, 8, "RW", 0, 2'h3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlCTg1_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlCTg1_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCALcdlAddDlySampEn_p2 extends uvm_reg;
	rand uvm_reg_field PclkDCALcdlAddDlySampEn_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   PclkDCALcdlAddDlySampEn_p2: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCALcdlAddDlySampEn_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PclkDCALcdlAddDlySampEn_p2 = uvm_reg_field::type_id::create("PclkDCALcdlAddDlySampEn_p2",,get_full_name());
      this.PclkDCALcdlAddDlySampEn_p2.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCALcdlAddDlySampEn_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCALcdlAddDlySampEn_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln0_p2 extends uvm_reg;
	rand uvm_reg_field TxDcaCoarseTg0Ln0;
	rand uvm_reg_field TxDcaFinePUTg0Ln0;
	rand uvm_reg_field TxDcaFinePDTg0Ln0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaCoarseTg0Ln0: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUTg0Ln0: coverpoint {m_data[5:2], m_is_read} iff(m_be) {
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
	   TxDcaFinePDTg0Ln0: coverpoint {m_data[9:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln0_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaCoarseTg0Ln0 = uvm_reg_field::type_id::create("TxDcaCoarseTg0Ln0",,get_full_name());
      this.TxDcaCoarseTg0Ln0.configure(this, 2, 0, "RW", 0, 2'h3, 1, 0, 0);
      this.TxDcaFinePUTg0Ln0 = uvm_reg_field::type_id::create("TxDcaFinePUTg0Ln0",,get_full_name());
      this.TxDcaFinePUTg0Ln0.configure(this, 4, 2, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePDTg0Ln0 = uvm_reg_field::type_id::create("TxDcaFinePDTg0Ln0",,get_full_name());
      this.TxDcaFinePDTg0Ln0.configure(this, 4, 6, "RW", 0, 4'h6, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln0_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln0_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln0_p2 extends uvm_reg;
	rand uvm_reg_field TxDcaCoarseTg1Ln0;
	rand uvm_reg_field TxDcaFinePUTg1Ln0;
	rand uvm_reg_field TxDcaFinePDTg1Ln0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaCoarseTg1Ln0: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUTg1Ln0: coverpoint {m_data[5:2], m_is_read} iff(m_be) {
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
	   TxDcaFinePDTg1Ln0: coverpoint {m_data[9:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln0_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaCoarseTg1Ln0 = uvm_reg_field::type_id::create("TxDcaCoarseTg1Ln0",,get_full_name());
      this.TxDcaCoarseTg1Ln0.configure(this, 2, 0, "RW", 0, 2'h3, 1, 0, 0);
      this.TxDcaFinePUTg1Ln0 = uvm_reg_field::type_id::create("TxDcaFinePUTg1Ln0",,get_full_name());
      this.TxDcaFinePUTg1Ln0.configure(this, 4, 2, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePDTg1Ln0 = uvm_reg_field::type_id::create("TxDcaFinePDTg1Ln0",,get_full_name());
      this.TxDcaFinePDTg1Ln0.configure(this, 4, 6, "RW", 0, 4'h6, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln0_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln0_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln1_p2 extends uvm_reg;
	rand uvm_reg_field TxDcaCoarseTg0Ln1;
	rand uvm_reg_field TxDcaFinePUTg0Ln1;
	rand uvm_reg_field TxDcaFinePDTg0Ln1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaCoarseTg0Ln1: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUTg0Ln1: coverpoint {m_data[5:2], m_is_read} iff(m_be) {
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
	   TxDcaFinePDTg0Ln1: coverpoint {m_data[9:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln1_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaCoarseTg0Ln1 = uvm_reg_field::type_id::create("TxDcaCoarseTg0Ln1",,get_full_name());
      this.TxDcaCoarseTg0Ln1.configure(this, 2, 0, "RW", 0, 2'h3, 1, 0, 0);
      this.TxDcaFinePUTg0Ln1 = uvm_reg_field::type_id::create("TxDcaFinePUTg0Ln1",,get_full_name());
      this.TxDcaFinePUTg0Ln1.configure(this, 4, 2, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePDTg0Ln1 = uvm_reg_field::type_id::create("TxDcaFinePDTg0Ln1",,get_full_name());
      this.TxDcaFinePDTg0Ln1.configure(this, 4, 6, "RW", 0, 4'h6, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln1_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln1_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln1_p2 extends uvm_reg;
	rand uvm_reg_field TxDcaCoarseTg1Ln1;
	rand uvm_reg_field TxDcaFinePUTg1Ln1;
	rand uvm_reg_field TxDcaFinePDTg1Ln1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaCoarseTg1Ln1: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUTg1Ln1: coverpoint {m_data[5:2], m_is_read} iff(m_be) {
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
	   TxDcaFinePDTg1Ln1: coverpoint {m_data[9:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln1_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaCoarseTg1Ln1 = uvm_reg_field::type_id::create("TxDcaCoarseTg1Ln1",,get_full_name());
      this.TxDcaCoarseTg1Ln1.configure(this, 2, 0, "RW", 0, 2'h3, 1, 0, 0);
      this.TxDcaFinePUTg1Ln1 = uvm_reg_field::type_id::create("TxDcaFinePUTg1Ln1",,get_full_name());
      this.TxDcaFinePUTg1Ln1.configure(this, 4, 2, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePDTg1Ln1 = uvm_reg_field::type_id::create("TxDcaFinePDTg1Ln1",,get_full_name());
      this.TxDcaFinePDTg1Ln1.configure(this, 4, 6, "RW", 0, 4'h6, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln1_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln1_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln2_p2 extends uvm_reg;
	rand uvm_reg_field TxDcaCoarseTg0Ln2;
	rand uvm_reg_field TxDcaFinePUTg0Ln2;
	rand uvm_reg_field TxDcaFinePDTg0Ln2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaCoarseTg0Ln2: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUTg0Ln2: coverpoint {m_data[5:2], m_is_read} iff(m_be) {
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
	   TxDcaFinePDTg0Ln2: coverpoint {m_data[9:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln2_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaCoarseTg0Ln2 = uvm_reg_field::type_id::create("TxDcaCoarseTg0Ln2",,get_full_name());
      this.TxDcaCoarseTg0Ln2.configure(this, 2, 0, "RW", 0, 2'h3, 1, 0, 0);
      this.TxDcaFinePUTg0Ln2 = uvm_reg_field::type_id::create("TxDcaFinePUTg0Ln2",,get_full_name());
      this.TxDcaFinePUTg0Ln2.configure(this, 4, 2, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePDTg0Ln2 = uvm_reg_field::type_id::create("TxDcaFinePDTg0Ln2",,get_full_name());
      this.TxDcaFinePDTg0Ln2.configure(this, 4, 6, "RW", 0, 4'h6, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln2_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln2_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln2_p2 extends uvm_reg;
	rand uvm_reg_field TxDcaCoarseTg1Ln2;
	rand uvm_reg_field TxDcaFinePUTg1Ln2;
	rand uvm_reg_field TxDcaFinePDTg1Ln2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaCoarseTg1Ln2: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUTg1Ln2: coverpoint {m_data[5:2], m_is_read} iff(m_be) {
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
	   TxDcaFinePDTg1Ln2: coverpoint {m_data[9:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln2_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaCoarseTg1Ln2 = uvm_reg_field::type_id::create("TxDcaCoarseTg1Ln2",,get_full_name());
      this.TxDcaCoarseTg1Ln2.configure(this, 2, 0, "RW", 0, 2'h3, 1, 0, 0);
      this.TxDcaFinePUTg1Ln2 = uvm_reg_field::type_id::create("TxDcaFinePUTg1Ln2",,get_full_name());
      this.TxDcaFinePUTg1Ln2.configure(this, 4, 2, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePDTg1Ln2 = uvm_reg_field::type_id::create("TxDcaFinePDTg1Ln2",,get_full_name());
      this.TxDcaFinePDTg1Ln2.configure(this, 4, 6, "RW", 0, 4'h6, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln2_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln2_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln3_p2 extends uvm_reg;
	rand uvm_reg_field TxDcaCoarseTg0Ln3;
	rand uvm_reg_field TxDcaFinePUTg0Ln3;
	rand uvm_reg_field TxDcaFinePDTg0Ln3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaCoarseTg0Ln3: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUTg0Ln3: coverpoint {m_data[5:2], m_is_read} iff(m_be) {
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
	   TxDcaFinePDTg0Ln3: coverpoint {m_data[9:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln3_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaCoarseTg0Ln3 = uvm_reg_field::type_id::create("TxDcaCoarseTg0Ln3",,get_full_name());
      this.TxDcaCoarseTg0Ln3.configure(this, 2, 0, "RW", 0, 2'h3, 1, 0, 0);
      this.TxDcaFinePUTg0Ln3 = uvm_reg_field::type_id::create("TxDcaFinePUTg0Ln3",,get_full_name());
      this.TxDcaFinePUTg0Ln3.configure(this, 4, 2, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePDTg0Ln3 = uvm_reg_field::type_id::create("TxDcaFinePDTg0Ln3",,get_full_name());
      this.TxDcaFinePDTg0Ln3.configure(this, 4, 6, "RW", 0, 4'h6, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln3_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln3_p2


class ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln3_p2 extends uvm_reg;
	rand uvm_reg_field TxDcaCoarseTg1Ln3;
	rand uvm_reg_field TxDcaFinePUTg1Ln3;
	rand uvm_reg_field TxDcaFinePDTg1Ln3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   TxDcaCoarseTg1Ln3: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   TxDcaFinePUTg1Ln3: coverpoint {m_data[5:2], m_is_read} iff(m_be) {
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
	   TxDcaFinePDTg1Ln3: coverpoint {m_data[9:6], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln3_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.TxDcaCoarseTg1Ln3 = uvm_reg_field::type_id::create("TxDcaCoarseTg1Ln3",,get_full_name());
      this.TxDcaCoarseTg1Ln3.configure(this, 2, 0, "RW", 0, 2'h3, 1, 0, 0);
      this.TxDcaFinePUTg1Ln3 = uvm_reg_field::type_id::create("TxDcaFinePUTg1Ln3",,get_full_name());
      this.TxDcaFinePUTg1Ln3.configure(this, 4, 2, "RW", 0, 4'h6, 1, 0, 0);
      this.TxDcaFinePDTg1Ln3 = uvm_reg_field::type_id::create("TxDcaFinePDTg1Ln3",,get_full_name());
      this.TxDcaFinePDTg1Ln3.configure(this, 4, 6, "RW", 0, 4'h6, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln3_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln3_p2


class ral_block_DWC_DDRPHYA_HMDBYTE4_2_p2 extends uvm_reg_block;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFECtrlDq_p2 RxDFECtrlDq_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_LpDqPowerDnDly_p2 LpDqPowerDnDly_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_DxDigStrobeMode_p2 DxDigStrobeMode_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_DqVregRsvdP_p2 DqVregRsvdP_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_EnaRxStrobeEnB_p2 EnaRxStrobeEnB_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDQSlew_p2 TxDQSlew_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxImpedanceDq_p2 TxImpedanceDq_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxImpedanceDqs_p2 TxImpedanceDqs_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_OdtImpedanceDq_p2 OdtImpedanceDq_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_OdtImpedanceDqs_p2 OdtImpedanceDqs_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDQSSeVrefDAC0_p2 RxDQSSeVrefDAC0_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDQSCtrl_p2 RxDQSCtrl_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDQDcaMode_p2 TxDQDcaMode_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMTxLcdlSeed_p2 HMTxLcdlSeed_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMRxLcdlSeed_p2 HMRxLcdlSeed_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_LcdlMonitorCtl_p2 LcdlMonitorCtl_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMDBYTELcdlCalDeltaMM_p2 HMDBYTELcdlCalDeltaMM_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn0_p2 RxOffsetSelEvenSLn0_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn1_p2 RxOffsetSelEvenSLn1_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn2_p2 RxOffsetSelEvenSLn2_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn3_p2 RxOffsetSelEvenSLn3_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn0_p2 RxOffsetSelOddSLn0_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn1_p2 RxOffsetSelOddSLn1_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn2_p2 RxOffsetSelOddSLn2_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn3_p2 RxOffsetSelOddSLn3_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMRxReplicaLcdlSeed_p2 HMRxReplicaLcdlSeed_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDiffDcaMode_p2 TxDiffDcaMode_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln0_p2 RxDFETap1SelTg0Ln0_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln0_p2 RxDFETap1SelTg1Ln0_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln0_p2 RxDFETap2SelTg0Ln0_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln0_p2 RxDFETap2SelTg1Ln0_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln1_p2 RxDFETap1SelTg0Ln1_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln1_p2 RxDFETap1SelTg1Ln1_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln1_p2 RxDFETap2SelTg0Ln1_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln1_p2 RxDFETap2SelTg1Ln1_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln2_p2 RxDFETap1SelTg0Ln2_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln2_p2 RxDFETap1SelTg1Ln2_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln2_p2 RxDFETap2SelTg0Ln2_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln2_p2 RxDFETap2SelTg1Ln2_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln3_p2 RxDFETap1SelTg0Ln3_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln3_p2 RxDFETap1SelTg1Ln3_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln3_p2 RxDFETap2SelTg0Ln3_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln3_p2 RxDFETap2SelTg1Ln3_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn0_p2 PclkDCACodeDqLn0_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn1_p2 PclkDCACodeDqLn1_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn2_p2 PclkDCACodeDqLn2_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn3_p2 PclkDCACodeDqLn3_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDQS_p2 PclkDCACodeDQS_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMReservedP1_p2 HMReservedP1_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCATxLcdlPhase_p2 PclkDCATxLcdlPhase_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn0_p2 PclkDCDOffsetDqLn0_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn1_p2 PclkDCDOffsetDqLn1_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn2_p2 PclkDCDOffsetDqLn2_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn3_p2 PclkDCDOffsetDqLn3_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDQS_p2 PclkDCDOffsetDQS_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTTg0_p2 TxDcaCtrlTTg0_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTTg1_p2 TxDcaCtrlTTg1_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlCTg0_p2 TxDcaCtrlCTg0_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlCTg1_p2 TxDcaCtrlCTg1_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlTTg0_p2 RxDcaCtrlTTg0_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlTTg1_p2 RxDcaCtrlTTg1_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlCTg0_p2 RxDcaCtrlCTg0_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlCTg1_p2 RxDcaCtrlCTg1_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCALcdlAddDlySampEn_p2 PclkDCALcdlAddDlySampEn_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln0_p2 TxDcaCtrlTg0Ln0_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln0_p2 TxDcaCtrlTg1Ln0_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln1_p2 TxDcaCtrlTg0Ln1_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln1_p2 TxDcaCtrlTg1Ln1_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln2_p2 TxDcaCtrlTg0Ln2_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln2_p2 TxDcaCtrlTg1Ln2_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln3_p2 TxDcaCtrlTg0Ln3_p2;
	rand ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln3_p2 TxDcaCtrlTg1Ln3_p2;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field RxDFECtrlDq_p2_RxDFECtrlDq_p2;
	rand uvm_reg_field LpDqPowerDnDly_p2_LpDqPowerDnDly_p2;
	rand uvm_reg_field DxDigStrobeMode_p2_DxDigStrobeMode_p2;
	rand uvm_reg_field DqVregRsvdP_p2_DqVregRsvdP_p2;
	rand uvm_reg_field EnaRxStrobeEnB_p2_EnaRxStrobeEnB_p2;
	rand uvm_reg_field TxDQSlew_p2_TxDQSlewPU;
	rand uvm_reg_field TxDQSlewPU;
	rand uvm_reg_field TxDQSlew_p2_TxDQSlewPD;
	rand uvm_reg_field TxDQSlewPD;
	rand uvm_reg_field TxImpedanceDq_p2_TxStrenCodeDqPU;
	rand uvm_reg_field TxStrenCodeDqPU;
	rand uvm_reg_field TxImpedanceDq_p2_TxStrenCodeDqPD;
	rand uvm_reg_field TxStrenCodeDqPD;
	rand uvm_reg_field TxImpedanceDqs_p2_TxStrenCodeDqsPUT;
	rand uvm_reg_field TxStrenCodeDqsPUT;
	rand uvm_reg_field TxImpedanceDqs_p2_TxStrenCodeDqsPUC;
	rand uvm_reg_field TxStrenCodeDqsPUC;
	rand uvm_reg_field TxImpedanceDqs_p2_TxStrenCodeDqsPDT;
	rand uvm_reg_field TxStrenCodeDqsPDT;
	rand uvm_reg_field TxImpedanceDqs_p2_TxStrenCodeDqsPDC;
	rand uvm_reg_field TxStrenCodeDqsPDC;
	rand uvm_reg_field OdtImpedanceDq_p2_OdtStrenCodeDqPU;
	rand uvm_reg_field OdtStrenCodeDqPU;
	rand uvm_reg_field OdtImpedanceDq_p2_OdtStrenCodeDqPD;
	rand uvm_reg_field OdtStrenCodeDqPD;
	rand uvm_reg_field OdtImpedanceDqs_p2_OdtStrenCodeDqsPUT;
	rand uvm_reg_field OdtStrenCodeDqsPUT;
	rand uvm_reg_field OdtImpedanceDqs_p2_OdtStrenCodeDqsPUC;
	rand uvm_reg_field OdtStrenCodeDqsPUC;
	rand uvm_reg_field OdtImpedanceDqs_p2_OdtStrenCodeDqsPDT;
	rand uvm_reg_field OdtStrenCodeDqsPDT;
	rand uvm_reg_field OdtImpedanceDqs_p2_OdtStrenCodeDqsPDC;
	rand uvm_reg_field OdtStrenCodeDqsPDC;
	rand uvm_reg_field RxDQSSeVrefDAC0_p2_RxDQSSeVrefDAC0_p2;
	rand uvm_reg_field RxDQSCtrl_p2_RxDQSDiffSeVrefDACEn;
	rand uvm_reg_field RxDQSDiffSeVrefDACEn;
	rand uvm_reg_field RxDQSCtrl_p2_RxDiffSeCtrl;
	rand uvm_reg_field RxDiffSeCtrl;
	rand uvm_reg_field TxDQDcaMode_p2_TxDQDcaMode_p2;
	rand uvm_reg_field HMTxLcdlSeed_p2_HMTxLcdlSeed_p2;
	rand uvm_reg_field HMRxLcdlSeed_p2_HMRxLcdlSeed_p2;
	rand uvm_reg_field LcdlMonitorCtl_p2_StickyUnlckThrshld;
	rand uvm_reg_field StickyUnlckThrshld;
	rand uvm_reg_field HMDBYTELcdlCalDeltaMM_p2_TxLcdlCalDeltaMM;
	rand uvm_reg_field TxLcdlCalDeltaMM;
	rand uvm_reg_field HMDBYTELcdlCalDeltaMM_p2_RxLcdlCalDeltaMM;
	rand uvm_reg_field RxLcdlCalDeltaMM;
	rand uvm_reg_field HMDBYTELcdlCalDeltaMM_p2_RxReplicaLcdlCalDeltaMM;
	rand uvm_reg_field RxReplicaLcdlCalDeltaMM;
	rand uvm_reg_field RxOffsetSelEvenSLn0_p2_RxOffsetSelEvenSLn0_p2;
	rand uvm_reg_field RxOffsetSelEvenSLn1_p2_RxOffsetSelEvenSLn1_p2;
	rand uvm_reg_field RxOffsetSelEvenSLn2_p2_RxOffsetSelEvenSLn2_p2;
	rand uvm_reg_field RxOffsetSelEvenSLn3_p2_RxOffsetSelEvenSLn3_p2;
	rand uvm_reg_field RxOffsetSelOddSLn0_p2_RxOffsetSelOddSLn0_p2;
	rand uvm_reg_field RxOffsetSelOddSLn1_p2_RxOffsetSelOddSLn1_p2;
	rand uvm_reg_field RxOffsetSelOddSLn2_p2_RxOffsetSelOddSLn2_p2;
	rand uvm_reg_field RxOffsetSelOddSLn3_p2_RxOffsetSelOddSLn3_p2;
	rand uvm_reg_field HMRxReplicaLcdlSeed_p2_HMRxReplicaLcdlSeed_p2;
	rand uvm_reg_field TxDiffDcaMode_p2_TxDiffDcaMode_p2;
	rand uvm_reg_field RxDFETap1SelTg0Ln0_p2_RxDFETap1SelTg0Ln0_p2;
	rand uvm_reg_field RxDFETap1SelTg1Ln0_p2_RxDFETap1SelTg1Ln0_p2;
	rand uvm_reg_field RxDFETap2SelTg0Ln0_p2_RxDFETap2SelTg0Ln0_p2;
	rand uvm_reg_field RxDFETap2SelTg1Ln0_p2_RxDFETap2SelTg1Ln0_p2;
	rand uvm_reg_field RxDFETap1SelTg0Ln1_p2_RxDFETap1SelTg0Ln1_p2;
	rand uvm_reg_field RxDFETap1SelTg1Ln1_p2_RxDFETap1SelTg1Ln1_p2;
	rand uvm_reg_field RxDFETap2SelTg0Ln1_p2_RxDFETap2SelTg0Ln1_p2;
	rand uvm_reg_field RxDFETap2SelTg1Ln1_p2_RxDFETap2SelTg1Ln1_p2;
	rand uvm_reg_field RxDFETap1SelTg0Ln2_p2_RxDFETap1SelTg0Ln2_p2;
	rand uvm_reg_field RxDFETap1SelTg1Ln2_p2_RxDFETap1SelTg1Ln2_p2;
	rand uvm_reg_field RxDFETap2SelTg0Ln2_p2_RxDFETap2SelTg0Ln2_p2;
	rand uvm_reg_field RxDFETap2SelTg1Ln2_p2_RxDFETap2SelTg1Ln2_p2;
	rand uvm_reg_field RxDFETap1SelTg0Ln3_p2_RxDFETap1SelTg0Ln3_p2;
	rand uvm_reg_field RxDFETap1SelTg1Ln3_p2_RxDFETap1SelTg1Ln3_p2;
	rand uvm_reg_field RxDFETap2SelTg0Ln3_p2_RxDFETap2SelTg0Ln3_p2;
	rand uvm_reg_field RxDFETap2SelTg1Ln3_p2_RxDFETap2SelTg1Ln3_p2;
	rand uvm_reg_field PclkDCACodeDqLn0_p2_PclkDCACoarseDqLn0;
	rand uvm_reg_field PclkDCACoarseDqLn0;
	rand uvm_reg_field PclkDCACodeDqLn0_p2_PclkDCAFineDqLn0;
	rand uvm_reg_field PclkDCAFineDqLn0;
	rand uvm_reg_field PclkDCACodeDqLn1_p2_PclkDCACoarseDqLn1;
	rand uvm_reg_field PclkDCACoarseDqLn1;
	rand uvm_reg_field PclkDCACodeDqLn1_p2_PclkDCAFineDqLn1;
	rand uvm_reg_field PclkDCAFineDqLn1;
	rand uvm_reg_field PclkDCACodeDqLn2_p2_PclkDCACoarseDqLn2;
	rand uvm_reg_field PclkDCACoarseDqLn2;
	rand uvm_reg_field PclkDCACodeDqLn2_p2_PclkDCAFineDqLn2;
	rand uvm_reg_field PclkDCAFineDqLn2;
	rand uvm_reg_field PclkDCACodeDqLn3_p2_PclkDCACoarseDqLn3;
	rand uvm_reg_field PclkDCACoarseDqLn3;
	rand uvm_reg_field PclkDCACodeDqLn3_p2_PclkDCAFineDqLn3;
	rand uvm_reg_field PclkDCAFineDqLn3;
	rand uvm_reg_field PclkDCACodeDQS_p2_PclkDCACoarseDQS;
	rand uvm_reg_field PclkDCACoarseDQS;
	rand uvm_reg_field PclkDCACodeDQS_p2_PclkDCAFineDQS;
	rand uvm_reg_field PclkDCAFineDQS;
	rand uvm_reg_field HMReservedP1_p2_HMReservedP1_p2;
	rand uvm_reg_field PclkDCATxLcdlPhase_p2_PclkDCATxLcdlPhase_p2;
	rand uvm_reg_field PclkDCDOffsetDqLn0_p2_PclkDCDOffsetDqLn0_p2;
	rand uvm_reg_field PclkDCDOffsetDqLn1_p2_PclkDCDOffsetDqLn1_p2;
	rand uvm_reg_field PclkDCDOffsetDqLn2_p2_PclkDCDOffsetDqLn2_p2;
	rand uvm_reg_field PclkDCDOffsetDqLn3_p2_PclkDCDOffsetDqLn3_p2;
	rand uvm_reg_field PclkDCDOffsetDQS_p2_PclkDCDOffsetDQS_p2;
	rand uvm_reg_field TxDcaCtrlTTg0_p2_TxDcaFinePDTTg0;
	rand uvm_reg_field TxDcaFinePDTTg0;
	rand uvm_reg_field TxDcaCtrlTTg0_p2_TxDcaFinePUTTg0;
	rand uvm_reg_field TxDcaFinePUTTg0;
	rand uvm_reg_field TxDcaCtrlTTg0_p2_TxDcaCoarseTTg0;
	rand uvm_reg_field TxDcaCoarseTTg0;
	rand uvm_reg_field TxDcaCtrlTTg1_p2_TxDcaFinePDTTg1;
	rand uvm_reg_field TxDcaFinePDTTg1;
	rand uvm_reg_field TxDcaCtrlTTg1_p2_TxDcaFinePUTTg1;
	rand uvm_reg_field TxDcaFinePUTTg1;
	rand uvm_reg_field TxDcaCtrlTTg1_p2_TxDcaCoarseTTg1;
	rand uvm_reg_field TxDcaCoarseTTg1;
	rand uvm_reg_field TxDcaCtrlCTg0_p2_TxDcaFinePDCTg0;
	rand uvm_reg_field TxDcaFinePDCTg0;
	rand uvm_reg_field TxDcaCtrlCTg0_p2_TxDcaFinePUCTg0;
	rand uvm_reg_field TxDcaFinePUCTg0;
	rand uvm_reg_field TxDcaCtrlCTg0_p2_TxDcaCoarseCTg0;
	rand uvm_reg_field TxDcaCoarseCTg0;
	rand uvm_reg_field TxDcaCtrlCTg1_p2_TxDcaFinePDCTg1;
	rand uvm_reg_field TxDcaFinePDCTg1;
	rand uvm_reg_field TxDcaCtrlCTg1_p2_TxDcaFinePUCTg1;
	rand uvm_reg_field TxDcaFinePUCTg1;
	rand uvm_reg_field TxDcaCtrlCTg1_p2_TxDcaCoarseCTg1;
	rand uvm_reg_field TxDcaCoarseCTg1;
	rand uvm_reg_field RxDcaCtrlTTg0_p2_RxDcaFinePDTTg0;
	rand uvm_reg_field RxDcaFinePDTTg0;
	rand uvm_reg_field RxDcaCtrlTTg0_p2_RxDcaFinePUTTg0;
	rand uvm_reg_field RxDcaFinePUTTg0;
	rand uvm_reg_field RxDcaCtrlTTg0_p2_RxDcaCoarseTTg0;
	rand uvm_reg_field RxDcaCoarseTTg0;
	rand uvm_reg_field RxDcaCtrlTTg1_p2_RxDcaFinePDTTg1;
	rand uvm_reg_field RxDcaFinePDTTg1;
	rand uvm_reg_field RxDcaCtrlTTg1_p2_RxDcaFinePUTTg1;
	rand uvm_reg_field RxDcaFinePUTTg1;
	rand uvm_reg_field RxDcaCtrlTTg1_p2_RxDcaCoarseTTg1;
	rand uvm_reg_field RxDcaCoarseTTg1;
	rand uvm_reg_field RxDcaCtrlCTg0_p2_RxDcaFinePDCTg0;
	rand uvm_reg_field RxDcaFinePDCTg0;
	rand uvm_reg_field RxDcaCtrlCTg0_p2_RxDcaFinePUCTg0;
	rand uvm_reg_field RxDcaFinePUCTg0;
	rand uvm_reg_field RxDcaCtrlCTg0_p2_RxDcaCoarseCTg0;
	rand uvm_reg_field RxDcaCoarseCTg0;
	rand uvm_reg_field RxDcaCtrlCTg1_p2_RxDcaFinePDCTg1;
	rand uvm_reg_field RxDcaFinePDCTg1;
	rand uvm_reg_field RxDcaCtrlCTg1_p2_RxDcaFinePUCTg1;
	rand uvm_reg_field RxDcaFinePUCTg1;
	rand uvm_reg_field RxDcaCtrlCTg1_p2_RxDcaCoarseCTg1;
	rand uvm_reg_field RxDcaCoarseCTg1;
	rand uvm_reg_field PclkDCALcdlAddDlySampEn_p2_PclkDCALcdlAddDlySampEn_p2;
	rand uvm_reg_field TxDcaCtrlTg0Ln0_p2_TxDcaCoarseTg0Ln0;
	rand uvm_reg_field TxDcaCoarseTg0Ln0;
	rand uvm_reg_field TxDcaCtrlTg0Ln0_p2_TxDcaFinePUTg0Ln0;
	rand uvm_reg_field TxDcaFinePUTg0Ln0;
	rand uvm_reg_field TxDcaCtrlTg0Ln0_p2_TxDcaFinePDTg0Ln0;
	rand uvm_reg_field TxDcaFinePDTg0Ln0;
	rand uvm_reg_field TxDcaCtrlTg1Ln0_p2_TxDcaCoarseTg1Ln0;
	rand uvm_reg_field TxDcaCoarseTg1Ln0;
	rand uvm_reg_field TxDcaCtrlTg1Ln0_p2_TxDcaFinePUTg1Ln0;
	rand uvm_reg_field TxDcaFinePUTg1Ln0;
	rand uvm_reg_field TxDcaCtrlTg1Ln0_p2_TxDcaFinePDTg1Ln0;
	rand uvm_reg_field TxDcaFinePDTg1Ln0;
	rand uvm_reg_field TxDcaCtrlTg0Ln1_p2_TxDcaCoarseTg0Ln1;
	rand uvm_reg_field TxDcaCoarseTg0Ln1;
	rand uvm_reg_field TxDcaCtrlTg0Ln1_p2_TxDcaFinePUTg0Ln1;
	rand uvm_reg_field TxDcaFinePUTg0Ln1;
	rand uvm_reg_field TxDcaCtrlTg0Ln1_p2_TxDcaFinePDTg0Ln1;
	rand uvm_reg_field TxDcaFinePDTg0Ln1;
	rand uvm_reg_field TxDcaCtrlTg1Ln1_p2_TxDcaCoarseTg1Ln1;
	rand uvm_reg_field TxDcaCoarseTg1Ln1;
	rand uvm_reg_field TxDcaCtrlTg1Ln1_p2_TxDcaFinePUTg1Ln1;
	rand uvm_reg_field TxDcaFinePUTg1Ln1;
	rand uvm_reg_field TxDcaCtrlTg1Ln1_p2_TxDcaFinePDTg1Ln1;
	rand uvm_reg_field TxDcaFinePDTg1Ln1;
	rand uvm_reg_field TxDcaCtrlTg0Ln2_p2_TxDcaCoarseTg0Ln2;
	rand uvm_reg_field TxDcaCoarseTg0Ln2;
	rand uvm_reg_field TxDcaCtrlTg0Ln2_p2_TxDcaFinePUTg0Ln2;
	rand uvm_reg_field TxDcaFinePUTg0Ln2;
	rand uvm_reg_field TxDcaCtrlTg0Ln2_p2_TxDcaFinePDTg0Ln2;
	rand uvm_reg_field TxDcaFinePDTg0Ln2;
	rand uvm_reg_field TxDcaCtrlTg1Ln2_p2_TxDcaCoarseTg1Ln2;
	rand uvm_reg_field TxDcaCoarseTg1Ln2;
	rand uvm_reg_field TxDcaCtrlTg1Ln2_p2_TxDcaFinePUTg1Ln2;
	rand uvm_reg_field TxDcaFinePUTg1Ln2;
	rand uvm_reg_field TxDcaCtrlTg1Ln2_p2_TxDcaFinePDTg1Ln2;
	rand uvm_reg_field TxDcaFinePDTg1Ln2;
	rand uvm_reg_field TxDcaCtrlTg0Ln3_p2_TxDcaCoarseTg0Ln3;
	rand uvm_reg_field TxDcaCoarseTg0Ln3;
	rand uvm_reg_field TxDcaCtrlTg0Ln3_p2_TxDcaFinePUTg0Ln3;
	rand uvm_reg_field TxDcaFinePUTg0Ln3;
	rand uvm_reg_field TxDcaCtrlTg0Ln3_p2_TxDcaFinePDTg0Ln3;
	rand uvm_reg_field TxDcaFinePDTg0Ln3;
	rand uvm_reg_field TxDcaCtrlTg1Ln3_p2_TxDcaCoarseTg1Ln3;
	rand uvm_reg_field TxDcaCoarseTg1Ln3;
	rand uvm_reg_field TxDcaCtrlTg1Ln3_p2_TxDcaFinePUTg1Ln3;
	rand uvm_reg_field TxDcaFinePUTg1Ln3;
	rand uvm_reg_field TxDcaCtrlTg1Ln3_p2_TxDcaFinePDTg1Ln3;
	rand uvm_reg_field TxDcaFinePDTg1Ln3;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	RxDFECtrlDq_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2 };
		option.weight = 1;
	}

	LpDqPowerDnDly_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5 };
		option.weight = 1;
	}

	DxDigStrobeMode_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB };
		option.weight = 1;
	}

	DqVregRsvdP_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h12 };
		option.weight = 1;
	}

	EnaRxStrobeEnB_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h13 };
		option.weight = 1;
	}

	TxDQSlew_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1C };
		option.weight = 1;
	}

	TxImpedanceDq_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2C };
		option.weight = 1;
	}

	TxImpedanceDqs_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2D };
		option.weight = 1;
	}

	OdtImpedanceDq_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2E };
		option.weight = 1;
	}

	OdtImpedanceDqs_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h2F };
		option.weight = 1;
	}

	RxDQSSeVrefDAC0_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3C };
		option.weight = 1;
	}

	RxDQSCtrl_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3E };
		option.weight = 1;
	}

	TxDQDcaMode_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h3F };
		option.weight = 1;
	}

	HMTxLcdlSeed_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h63 };
		option.weight = 1;
	}

	HMRxLcdlSeed_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h64 };
		option.weight = 1;
	}

	LcdlMonitorCtl_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h66 };
		option.weight = 1;
	}

	HMDBYTELcdlCalDeltaMM_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h67 };
		option.weight = 1;
	}

	RxOffsetSelEvenSLn0_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h70 };
		option.weight = 1;
	}

	RxOffsetSelEvenSLn1_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h71 };
		option.weight = 1;
	}

	RxOffsetSelEvenSLn2_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h72 };
		option.weight = 1;
	}

	RxOffsetSelEvenSLn3_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h73 };
		option.weight = 1;
	}

	RxOffsetSelOddSLn0_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h75 };
		option.weight = 1;
	}

	RxOffsetSelOddSLn1_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h76 };
		option.weight = 1;
	}

	RxOffsetSelOddSLn2_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h77 };
		option.weight = 1;
	}

	RxOffsetSelOddSLn3_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h78 };
		option.weight = 1;
	}

	HMRxReplicaLcdlSeed_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h87 };
		option.weight = 1;
	}

	TxDiffDcaMode_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h8D };
		option.weight = 1;
	}

	RxDFETap1SelTg0Ln0_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA0 };
		option.weight = 1;
	}

	RxDFETap1SelTg1Ln0_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA1 };
		option.weight = 1;
	}

	RxDFETap2SelTg0Ln0_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA4 };
		option.weight = 1;
	}

	RxDFETap2SelTg1Ln0_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA5 };
		option.weight = 1;
	}

	RxDFETap1SelTg0Ln1_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB0 };
		option.weight = 1;
	}

	RxDFETap1SelTg1Ln1_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB1 };
		option.weight = 1;
	}

	RxDFETap2SelTg0Ln1_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB4 };
		option.weight = 1;
	}

	RxDFETap2SelTg1Ln1_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB5 };
		option.weight = 1;
	}

	RxDFETap1SelTg0Ln2_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC0 };
		option.weight = 1;
	}

	RxDFETap1SelTg1Ln2_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC1 };
		option.weight = 1;
	}

	RxDFETap2SelTg0Ln2_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC4 };
		option.weight = 1;
	}

	RxDFETap2SelTg1Ln2_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC5 };
		option.weight = 1;
	}

	RxDFETap1SelTg0Ln3_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD0 };
		option.weight = 1;
	}

	RxDFETap1SelTg1Ln3_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD1 };
		option.weight = 1;
	}

	RxDFETap2SelTg0Ln3_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD4 };
		option.weight = 1;
	}

	RxDFETap2SelTg1Ln3_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD5 };
		option.weight = 1;
	}

	PclkDCACodeDqLn0_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF0 };
		option.weight = 1;
	}

	PclkDCACodeDqLn1_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF1 };
		option.weight = 1;
	}

	PclkDCACodeDqLn2_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF2 };
		option.weight = 1;
	}

	PclkDCACodeDqLn3_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF3 };
		option.weight = 1;
	}

	PclkDCACodeDQS_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF5 };
		option.weight = 1;
	}

	HMReservedP1_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFF };
		option.weight = 1;
	}

	PclkDCATxLcdlPhase_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h110 };
		option.weight = 1;
	}

	PclkDCDOffsetDqLn0_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h200 };
		option.weight = 1;
	}

	PclkDCDOffsetDqLn1_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h201 };
		option.weight = 1;
	}

	PclkDCDOffsetDqLn2_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h202 };
		option.weight = 1;
	}

	PclkDCDOffsetDqLn3_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h203 };
		option.weight = 1;
	}

	PclkDCDOffsetDQS_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h205 };
		option.weight = 1;
	}

	TxDcaCtrlTTg0_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h550 };
		option.weight = 1;
	}

	TxDcaCtrlTTg1_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h551 };
		option.weight = 1;
	}

	TxDcaCtrlCTg0_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h560 };
		option.weight = 1;
	}

	TxDcaCtrlCTg1_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h561 };
		option.weight = 1;
	}

	RxDcaCtrlTTg0_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h570 };
		option.weight = 1;
	}

	RxDcaCtrlTTg1_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h571 };
		option.weight = 1;
	}

	RxDcaCtrlCTg0_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h580 };
		option.weight = 1;
	}

	RxDcaCtrlCTg1_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h581 };
		option.weight = 1;
	}

	PclkDCALcdlAddDlySampEn_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5E3 };
		option.weight = 1;
	}

	TxDcaCtrlTg0Ln0_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h600 };
		option.weight = 1;
	}

	TxDcaCtrlTg1Ln0_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h601 };
		option.weight = 1;
	}

	TxDcaCtrlTg0Ln1_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h610 };
		option.weight = 1;
	}

	TxDcaCtrlTg1Ln1_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h611 };
		option.weight = 1;
	}

	TxDcaCtrlTg0Ln2_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h620 };
		option.weight = 1;
	}

	TxDcaCtrlTg1Ln2_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h621 };
		option.weight = 1;
	}

	TxDcaCtrlTg0Ln3_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h630 };
		option.weight = 1;
	}

	TxDcaCtrlTg1Ln3_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h631 };
		option.weight = 1;
	}
endgroup
	function new(string name = "DWC_DDRPHYA_HMDBYTE4_2_p2");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.RxDFECtrlDq_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFECtrlDq_p2::type_id::create("RxDFECtrlDq_p2",,get_full_name());
      if(this.RxDFECtrlDq_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDFECtrlDq_p2.cg_bits.option.name = {get_name(), ".", "RxDFECtrlDq_p2_bits"};
      this.RxDFECtrlDq_p2.configure(this, null, "");
      this.RxDFECtrlDq_p2.build();
      this.default_map.add_reg(this.RxDFECtrlDq_p2, `UVM_REG_ADDR_WIDTH'h2, "RW", 0);
		this.RxDFECtrlDq_p2_RxDFECtrlDq_p2 = this.RxDFECtrlDq_p2.RxDFECtrlDq_p2;
      this.LpDqPowerDnDly_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_LpDqPowerDnDly_p2::type_id::create("LpDqPowerDnDly_p2",,get_full_name());
      if(this.LpDqPowerDnDly_p2.has_coverage(UVM_CVR_ALL))
      	this.LpDqPowerDnDly_p2.cg_bits.option.name = {get_name(), ".", "LpDqPowerDnDly_p2_bits"};
      this.LpDqPowerDnDly_p2.configure(this, null, "");
      this.LpDqPowerDnDly_p2.build();
      this.default_map.add_reg(this.LpDqPowerDnDly_p2, `UVM_REG_ADDR_WIDTH'h5, "RW", 0);
		this.LpDqPowerDnDly_p2_LpDqPowerDnDly_p2 = this.LpDqPowerDnDly_p2.LpDqPowerDnDly_p2;
      this.DxDigStrobeMode_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_DxDigStrobeMode_p2::type_id::create("DxDigStrobeMode_p2",,get_full_name());
      if(this.DxDigStrobeMode_p2.has_coverage(UVM_CVR_ALL))
      	this.DxDigStrobeMode_p2.cg_bits.option.name = {get_name(), ".", "DxDigStrobeMode_p2_bits"};
      this.DxDigStrobeMode_p2.configure(this, null, "");
      this.DxDigStrobeMode_p2.build();
      this.default_map.add_reg(this.DxDigStrobeMode_p2, `UVM_REG_ADDR_WIDTH'hB, "RW", 0);
		this.DxDigStrobeMode_p2_DxDigStrobeMode_p2 = this.DxDigStrobeMode_p2.DxDigStrobeMode_p2;
      this.DqVregRsvdP_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_DqVregRsvdP_p2::type_id::create("DqVregRsvdP_p2",,get_full_name());
      if(this.DqVregRsvdP_p2.has_coverage(UVM_CVR_ALL))
      	this.DqVregRsvdP_p2.cg_bits.option.name = {get_name(), ".", "DqVregRsvdP_p2_bits"};
      this.DqVregRsvdP_p2.configure(this, null, "");
      this.DqVregRsvdP_p2.build();
      this.default_map.add_reg(this.DqVregRsvdP_p2, `UVM_REG_ADDR_WIDTH'h12, "RW", 0);
		this.DqVregRsvdP_p2_DqVregRsvdP_p2 = this.DqVregRsvdP_p2.DqVregRsvdP_p2;
      this.EnaRxStrobeEnB_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_EnaRxStrobeEnB_p2::type_id::create("EnaRxStrobeEnB_p2",,get_full_name());
      if(this.EnaRxStrobeEnB_p2.has_coverage(UVM_CVR_ALL))
      	this.EnaRxStrobeEnB_p2.cg_bits.option.name = {get_name(), ".", "EnaRxStrobeEnB_p2_bits"};
      this.EnaRxStrobeEnB_p2.configure(this, null, "");
      this.EnaRxStrobeEnB_p2.build();
      this.default_map.add_reg(this.EnaRxStrobeEnB_p2, `UVM_REG_ADDR_WIDTH'h13, "RW", 0);
		this.EnaRxStrobeEnB_p2_EnaRxStrobeEnB_p2 = this.EnaRxStrobeEnB_p2.EnaRxStrobeEnB_p2;
      this.TxDQSlew_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDQSlew_p2::type_id::create("TxDQSlew_p2",,get_full_name());
      if(this.TxDQSlew_p2.has_coverage(UVM_CVR_ALL))
      	this.TxDQSlew_p2.cg_bits.option.name = {get_name(), ".", "TxDQSlew_p2_bits"};
      this.TxDQSlew_p2.configure(this, null, "");
      this.TxDQSlew_p2.build();
      this.default_map.add_reg(this.TxDQSlew_p2, `UVM_REG_ADDR_WIDTH'h1C, "RW", 0);
		this.TxDQSlew_p2_TxDQSlewPU = this.TxDQSlew_p2.TxDQSlewPU;
		this.TxDQSlewPU = this.TxDQSlew_p2.TxDQSlewPU;
		this.TxDQSlew_p2_TxDQSlewPD = this.TxDQSlew_p2.TxDQSlewPD;
		this.TxDQSlewPD = this.TxDQSlew_p2.TxDQSlewPD;
      this.TxImpedanceDq_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxImpedanceDq_p2::type_id::create("TxImpedanceDq_p2",,get_full_name());
      if(this.TxImpedanceDq_p2.has_coverage(UVM_CVR_ALL))
      	this.TxImpedanceDq_p2.cg_bits.option.name = {get_name(), ".", "TxImpedanceDq_p2_bits"};
      this.TxImpedanceDq_p2.configure(this, null, "");
      this.TxImpedanceDq_p2.build();
      this.default_map.add_reg(this.TxImpedanceDq_p2, `UVM_REG_ADDR_WIDTH'h2C, "RW", 0);
		this.TxImpedanceDq_p2_TxStrenCodeDqPU = this.TxImpedanceDq_p2.TxStrenCodeDqPU;
		this.TxStrenCodeDqPU = this.TxImpedanceDq_p2.TxStrenCodeDqPU;
		this.TxImpedanceDq_p2_TxStrenCodeDqPD = this.TxImpedanceDq_p2.TxStrenCodeDqPD;
		this.TxStrenCodeDqPD = this.TxImpedanceDq_p2.TxStrenCodeDqPD;
      this.TxImpedanceDqs_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxImpedanceDqs_p2::type_id::create("TxImpedanceDqs_p2",,get_full_name());
      if(this.TxImpedanceDqs_p2.has_coverage(UVM_CVR_ALL))
      	this.TxImpedanceDqs_p2.cg_bits.option.name = {get_name(), ".", "TxImpedanceDqs_p2_bits"};
      this.TxImpedanceDqs_p2.configure(this, null, "");
      this.TxImpedanceDqs_p2.build();
      this.default_map.add_reg(this.TxImpedanceDqs_p2, `UVM_REG_ADDR_WIDTH'h2D, "RW", 0);
		this.TxImpedanceDqs_p2_TxStrenCodeDqsPUT = this.TxImpedanceDqs_p2.TxStrenCodeDqsPUT;
		this.TxStrenCodeDqsPUT = this.TxImpedanceDqs_p2.TxStrenCodeDqsPUT;
		this.TxImpedanceDqs_p2_TxStrenCodeDqsPUC = this.TxImpedanceDqs_p2.TxStrenCodeDqsPUC;
		this.TxStrenCodeDqsPUC = this.TxImpedanceDqs_p2.TxStrenCodeDqsPUC;
		this.TxImpedanceDqs_p2_TxStrenCodeDqsPDT = this.TxImpedanceDqs_p2.TxStrenCodeDqsPDT;
		this.TxStrenCodeDqsPDT = this.TxImpedanceDqs_p2.TxStrenCodeDqsPDT;
		this.TxImpedanceDqs_p2_TxStrenCodeDqsPDC = this.TxImpedanceDqs_p2.TxStrenCodeDqsPDC;
		this.TxStrenCodeDqsPDC = this.TxImpedanceDqs_p2.TxStrenCodeDqsPDC;
      this.OdtImpedanceDq_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_OdtImpedanceDq_p2::type_id::create("OdtImpedanceDq_p2",,get_full_name());
      if(this.OdtImpedanceDq_p2.has_coverage(UVM_CVR_ALL))
      	this.OdtImpedanceDq_p2.cg_bits.option.name = {get_name(), ".", "OdtImpedanceDq_p2_bits"};
      this.OdtImpedanceDq_p2.configure(this, null, "");
      this.OdtImpedanceDq_p2.build();
      this.default_map.add_reg(this.OdtImpedanceDq_p2, `UVM_REG_ADDR_WIDTH'h2E, "RW", 0);
		this.OdtImpedanceDq_p2_OdtStrenCodeDqPU = this.OdtImpedanceDq_p2.OdtStrenCodeDqPU;
		this.OdtStrenCodeDqPU = this.OdtImpedanceDq_p2.OdtStrenCodeDqPU;
		this.OdtImpedanceDq_p2_OdtStrenCodeDqPD = this.OdtImpedanceDq_p2.OdtStrenCodeDqPD;
		this.OdtStrenCodeDqPD = this.OdtImpedanceDq_p2.OdtStrenCodeDqPD;
      this.OdtImpedanceDqs_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_OdtImpedanceDqs_p2::type_id::create("OdtImpedanceDqs_p2",,get_full_name());
      if(this.OdtImpedanceDqs_p2.has_coverage(UVM_CVR_ALL))
      	this.OdtImpedanceDqs_p2.cg_bits.option.name = {get_name(), ".", "OdtImpedanceDqs_p2_bits"};
      this.OdtImpedanceDqs_p2.configure(this, null, "");
      this.OdtImpedanceDqs_p2.build();
      this.default_map.add_reg(this.OdtImpedanceDqs_p2, `UVM_REG_ADDR_WIDTH'h2F, "RW", 0);
		this.OdtImpedanceDqs_p2_OdtStrenCodeDqsPUT = this.OdtImpedanceDqs_p2.OdtStrenCodeDqsPUT;
		this.OdtStrenCodeDqsPUT = this.OdtImpedanceDqs_p2.OdtStrenCodeDqsPUT;
		this.OdtImpedanceDqs_p2_OdtStrenCodeDqsPUC = this.OdtImpedanceDqs_p2.OdtStrenCodeDqsPUC;
		this.OdtStrenCodeDqsPUC = this.OdtImpedanceDqs_p2.OdtStrenCodeDqsPUC;
		this.OdtImpedanceDqs_p2_OdtStrenCodeDqsPDT = this.OdtImpedanceDqs_p2.OdtStrenCodeDqsPDT;
		this.OdtStrenCodeDqsPDT = this.OdtImpedanceDqs_p2.OdtStrenCodeDqsPDT;
		this.OdtImpedanceDqs_p2_OdtStrenCodeDqsPDC = this.OdtImpedanceDqs_p2.OdtStrenCodeDqsPDC;
		this.OdtStrenCodeDqsPDC = this.OdtImpedanceDqs_p2.OdtStrenCodeDqsPDC;
      this.RxDQSSeVrefDAC0_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDQSSeVrefDAC0_p2::type_id::create("RxDQSSeVrefDAC0_p2",,get_full_name());
      if(this.RxDQSSeVrefDAC0_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDQSSeVrefDAC0_p2.cg_bits.option.name = {get_name(), ".", "RxDQSSeVrefDAC0_p2_bits"};
      this.RxDQSSeVrefDAC0_p2.configure(this, null, "");
      this.RxDQSSeVrefDAC0_p2.build();
      this.default_map.add_reg(this.RxDQSSeVrefDAC0_p2, `UVM_REG_ADDR_WIDTH'h3C, "RW", 0);
		this.RxDQSSeVrefDAC0_p2_RxDQSSeVrefDAC0_p2 = this.RxDQSSeVrefDAC0_p2.RxDQSSeVrefDAC0_p2;
      this.RxDQSCtrl_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDQSCtrl_p2::type_id::create("RxDQSCtrl_p2",,get_full_name());
      if(this.RxDQSCtrl_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDQSCtrl_p2.cg_bits.option.name = {get_name(), ".", "RxDQSCtrl_p2_bits"};
      this.RxDQSCtrl_p2.configure(this, null, "");
      this.RxDQSCtrl_p2.build();
      this.default_map.add_reg(this.RxDQSCtrl_p2, `UVM_REG_ADDR_WIDTH'h3E, "RW", 0);
		this.RxDQSCtrl_p2_RxDQSDiffSeVrefDACEn = this.RxDQSCtrl_p2.RxDQSDiffSeVrefDACEn;
		this.RxDQSDiffSeVrefDACEn = this.RxDQSCtrl_p2.RxDQSDiffSeVrefDACEn;
		this.RxDQSCtrl_p2_RxDiffSeCtrl = this.RxDQSCtrl_p2.RxDiffSeCtrl;
		this.RxDiffSeCtrl = this.RxDQSCtrl_p2.RxDiffSeCtrl;
      this.TxDQDcaMode_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDQDcaMode_p2::type_id::create("TxDQDcaMode_p2",,get_full_name());
      if(this.TxDQDcaMode_p2.has_coverage(UVM_CVR_ALL))
      	this.TxDQDcaMode_p2.cg_bits.option.name = {get_name(), ".", "TxDQDcaMode_p2_bits"};
      this.TxDQDcaMode_p2.configure(this, null, "");
      this.TxDQDcaMode_p2.build();
      this.default_map.add_reg(this.TxDQDcaMode_p2, `UVM_REG_ADDR_WIDTH'h3F, "RW", 0);
		this.TxDQDcaMode_p2_TxDQDcaMode_p2 = this.TxDQDcaMode_p2.TxDQDcaMode_p2;
      this.HMTxLcdlSeed_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMTxLcdlSeed_p2::type_id::create("HMTxLcdlSeed_p2",,get_full_name());
      if(this.HMTxLcdlSeed_p2.has_coverage(UVM_CVR_ALL))
      	this.HMTxLcdlSeed_p2.cg_bits.option.name = {get_name(), ".", "HMTxLcdlSeed_p2_bits"};
      this.HMTxLcdlSeed_p2.configure(this, null, "");
      this.HMTxLcdlSeed_p2.build();
      this.default_map.add_reg(this.HMTxLcdlSeed_p2, `UVM_REG_ADDR_WIDTH'h63, "RW", 0);
		this.HMTxLcdlSeed_p2_HMTxLcdlSeed_p2 = this.HMTxLcdlSeed_p2.HMTxLcdlSeed_p2;
      this.HMRxLcdlSeed_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMRxLcdlSeed_p2::type_id::create("HMRxLcdlSeed_p2",,get_full_name());
      if(this.HMRxLcdlSeed_p2.has_coverage(UVM_CVR_ALL))
      	this.HMRxLcdlSeed_p2.cg_bits.option.name = {get_name(), ".", "HMRxLcdlSeed_p2_bits"};
      this.HMRxLcdlSeed_p2.configure(this, null, "");
      this.HMRxLcdlSeed_p2.build();
      this.default_map.add_reg(this.HMRxLcdlSeed_p2, `UVM_REG_ADDR_WIDTH'h64, "RW", 0);
		this.HMRxLcdlSeed_p2_HMRxLcdlSeed_p2 = this.HMRxLcdlSeed_p2.HMRxLcdlSeed_p2;
      this.LcdlMonitorCtl_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_LcdlMonitorCtl_p2::type_id::create("LcdlMonitorCtl_p2",,get_full_name());
      if(this.LcdlMonitorCtl_p2.has_coverage(UVM_CVR_ALL))
      	this.LcdlMonitorCtl_p2.cg_bits.option.name = {get_name(), ".", "LcdlMonitorCtl_p2_bits"};
      this.LcdlMonitorCtl_p2.configure(this, null, "");
      this.LcdlMonitorCtl_p2.build();
      this.default_map.add_reg(this.LcdlMonitorCtl_p2, `UVM_REG_ADDR_WIDTH'h66, "RW", 0);
		this.LcdlMonitorCtl_p2_StickyUnlckThrshld = this.LcdlMonitorCtl_p2.StickyUnlckThrshld;
		this.StickyUnlckThrshld = this.LcdlMonitorCtl_p2.StickyUnlckThrshld;
      this.HMDBYTELcdlCalDeltaMM_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMDBYTELcdlCalDeltaMM_p2::type_id::create("HMDBYTELcdlCalDeltaMM_p2",,get_full_name());
      if(this.HMDBYTELcdlCalDeltaMM_p2.has_coverage(UVM_CVR_ALL))
      	this.HMDBYTELcdlCalDeltaMM_p2.cg_bits.option.name = {get_name(), ".", "HMDBYTELcdlCalDeltaMM_p2_bits"};
      this.HMDBYTELcdlCalDeltaMM_p2.configure(this, null, "");
      this.HMDBYTELcdlCalDeltaMM_p2.build();
      this.default_map.add_reg(this.HMDBYTELcdlCalDeltaMM_p2, `UVM_REG_ADDR_WIDTH'h67, "RW", 0);
		this.HMDBYTELcdlCalDeltaMM_p2_TxLcdlCalDeltaMM = this.HMDBYTELcdlCalDeltaMM_p2.TxLcdlCalDeltaMM;
		this.TxLcdlCalDeltaMM = this.HMDBYTELcdlCalDeltaMM_p2.TxLcdlCalDeltaMM;
		this.HMDBYTELcdlCalDeltaMM_p2_RxLcdlCalDeltaMM = this.HMDBYTELcdlCalDeltaMM_p2.RxLcdlCalDeltaMM;
		this.RxLcdlCalDeltaMM = this.HMDBYTELcdlCalDeltaMM_p2.RxLcdlCalDeltaMM;
		this.HMDBYTELcdlCalDeltaMM_p2_RxReplicaLcdlCalDeltaMM = this.HMDBYTELcdlCalDeltaMM_p2.RxReplicaLcdlCalDeltaMM;
		this.RxReplicaLcdlCalDeltaMM = this.HMDBYTELcdlCalDeltaMM_p2.RxReplicaLcdlCalDeltaMM;
      this.RxOffsetSelEvenSLn0_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn0_p2::type_id::create("RxOffsetSelEvenSLn0_p2",,get_full_name());
      if(this.RxOffsetSelEvenSLn0_p2.has_coverage(UVM_CVR_ALL))
      	this.RxOffsetSelEvenSLn0_p2.cg_bits.option.name = {get_name(), ".", "RxOffsetSelEvenSLn0_p2_bits"};
      this.RxOffsetSelEvenSLn0_p2.configure(this, null, "");
      this.RxOffsetSelEvenSLn0_p2.build();
      this.default_map.add_reg(this.RxOffsetSelEvenSLn0_p2, `UVM_REG_ADDR_WIDTH'h70, "RW", 0);
		this.RxOffsetSelEvenSLn0_p2_RxOffsetSelEvenSLn0_p2 = this.RxOffsetSelEvenSLn0_p2.RxOffsetSelEvenSLn0_p2;
      this.RxOffsetSelEvenSLn1_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn1_p2::type_id::create("RxOffsetSelEvenSLn1_p2",,get_full_name());
      if(this.RxOffsetSelEvenSLn1_p2.has_coverage(UVM_CVR_ALL))
      	this.RxOffsetSelEvenSLn1_p2.cg_bits.option.name = {get_name(), ".", "RxOffsetSelEvenSLn1_p2_bits"};
      this.RxOffsetSelEvenSLn1_p2.configure(this, null, "");
      this.RxOffsetSelEvenSLn1_p2.build();
      this.default_map.add_reg(this.RxOffsetSelEvenSLn1_p2, `UVM_REG_ADDR_WIDTH'h71, "RW", 0);
		this.RxOffsetSelEvenSLn1_p2_RxOffsetSelEvenSLn1_p2 = this.RxOffsetSelEvenSLn1_p2.RxOffsetSelEvenSLn1_p2;
      this.RxOffsetSelEvenSLn2_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn2_p2::type_id::create("RxOffsetSelEvenSLn2_p2",,get_full_name());
      if(this.RxOffsetSelEvenSLn2_p2.has_coverage(UVM_CVR_ALL))
      	this.RxOffsetSelEvenSLn2_p2.cg_bits.option.name = {get_name(), ".", "RxOffsetSelEvenSLn2_p2_bits"};
      this.RxOffsetSelEvenSLn2_p2.configure(this, null, "");
      this.RxOffsetSelEvenSLn2_p2.build();
      this.default_map.add_reg(this.RxOffsetSelEvenSLn2_p2, `UVM_REG_ADDR_WIDTH'h72, "RW", 0);
		this.RxOffsetSelEvenSLn2_p2_RxOffsetSelEvenSLn2_p2 = this.RxOffsetSelEvenSLn2_p2.RxOffsetSelEvenSLn2_p2;
      this.RxOffsetSelEvenSLn3_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelEvenSLn3_p2::type_id::create("RxOffsetSelEvenSLn3_p2",,get_full_name());
      if(this.RxOffsetSelEvenSLn3_p2.has_coverage(UVM_CVR_ALL))
      	this.RxOffsetSelEvenSLn3_p2.cg_bits.option.name = {get_name(), ".", "RxOffsetSelEvenSLn3_p2_bits"};
      this.RxOffsetSelEvenSLn3_p2.configure(this, null, "");
      this.RxOffsetSelEvenSLn3_p2.build();
      this.default_map.add_reg(this.RxOffsetSelEvenSLn3_p2, `UVM_REG_ADDR_WIDTH'h73, "RW", 0);
		this.RxOffsetSelEvenSLn3_p2_RxOffsetSelEvenSLn3_p2 = this.RxOffsetSelEvenSLn3_p2.RxOffsetSelEvenSLn3_p2;
      this.RxOffsetSelOddSLn0_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn0_p2::type_id::create("RxOffsetSelOddSLn0_p2",,get_full_name());
      if(this.RxOffsetSelOddSLn0_p2.has_coverage(UVM_CVR_ALL))
      	this.RxOffsetSelOddSLn0_p2.cg_bits.option.name = {get_name(), ".", "RxOffsetSelOddSLn0_p2_bits"};
      this.RxOffsetSelOddSLn0_p2.configure(this, null, "");
      this.RxOffsetSelOddSLn0_p2.build();
      this.default_map.add_reg(this.RxOffsetSelOddSLn0_p2, `UVM_REG_ADDR_WIDTH'h75, "RW", 0);
		this.RxOffsetSelOddSLn0_p2_RxOffsetSelOddSLn0_p2 = this.RxOffsetSelOddSLn0_p2.RxOffsetSelOddSLn0_p2;
      this.RxOffsetSelOddSLn1_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn1_p2::type_id::create("RxOffsetSelOddSLn1_p2",,get_full_name());
      if(this.RxOffsetSelOddSLn1_p2.has_coverage(UVM_CVR_ALL))
      	this.RxOffsetSelOddSLn1_p2.cg_bits.option.name = {get_name(), ".", "RxOffsetSelOddSLn1_p2_bits"};
      this.RxOffsetSelOddSLn1_p2.configure(this, null, "");
      this.RxOffsetSelOddSLn1_p2.build();
      this.default_map.add_reg(this.RxOffsetSelOddSLn1_p2, `UVM_REG_ADDR_WIDTH'h76, "RW", 0);
		this.RxOffsetSelOddSLn1_p2_RxOffsetSelOddSLn1_p2 = this.RxOffsetSelOddSLn1_p2.RxOffsetSelOddSLn1_p2;
      this.RxOffsetSelOddSLn2_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn2_p2::type_id::create("RxOffsetSelOddSLn2_p2",,get_full_name());
      if(this.RxOffsetSelOddSLn2_p2.has_coverage(UVM_CVR_ALL))
      	this.RxOffsetSelOddSLn2_p2.cg_bits.option.name = {get_name(), ".", "RxOffsetSelOddSLn2_p2_bits"};
      this.RxOffsetSelOddSLn2_p2.configure(this, null, "");
      this.RxOffsetSelOddSLn2_p2.build();
      this.default_map.add_reg(this.RxOffsetSelOddSLn2_p2, `UVM_REG_ADDR_WIDTH'h77, "RW", 0);
		this.RxOffsetSelOddSLn2_p2_RxOffsetSelOddSLn2_p2 = this.RxOffsetSelOddSLn2_p2.RxOffsetSelOddSLn2_p2;
      this.RxOffsetSelOddSLn3_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxOffsetSelOddSLn3_p2::type_id::create("RxOffsetSelOddSLn3_p2",,get_full_name());
      if(this.RxOffsetSelOddSLn3_p2.has_coverage(UVM_CVR_ALL))
      	this.RxOffsetSelOddSLn3_p2.cg_bits.option.name = {get_name(), ".", "RxOffsetSelOddSLn3_p2_bits"};
      this.RxOffsetSelOddSLn3_p2.configure(this, null, "");
      this.RxOffsetSelOddSLn3_p2.build();
      this.default_map.add_reg(this.RxOffsetSelOddSLn3_p2, `UVM_REG_ADDR_WIDTH'h78, "RW", 0);
		this.RxOffsetSelOddSLn3_p2_RxOffsetSelOddSLn3_p2 = this.RxOffsetSelOddSLn3_p2.RxOffsetSelOddSLn3_p2;
      this.HMRxReplicaLcdlSeed_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMRxReplicaLcdlSeed_p2::type_id::create("HMRxReplicaLcdlSeed_p2",,get_full_name());
      if(this.HMRxReplicaLcdlSeed_p2.has_coverage(UVM_CVR_ALL))
      	this.HMRxReplicaLcdlSeed_p2.cg_bits.option.name = {get_name(), ".", "HMRxReplicaLcdlSeed_p2_bits"};
      this.HMRxReplicaLcdlSeed_p2.configure(this, null, "");
      this.HMRxReplicaLcdlSeed_p2.build();
      this.default_map.add_reg(this.HMRxReplicaLcdlSeed_p2, `UVM_REG_ADDR_WIDTH'h87, "RW", 0);
		this.HMRxReplicaLcdlSeed_p2_HMRxReplicaLcdlSeed_p2 = this.HMRxReplicaLcdlSeed_p2.HMRxReplicaLcdlSeed_p2;
      this.TxDiffDcaMode_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDiffDcaMode_p2::type_id::create("TxDiffDcaMode_p2",,get_full_name());
      if(this.TxDiffDcaMode_p2.has_coverage(UVM_CVR_ALL))
      	this.TxDiffDcaMode_p2.cg_bits.option.name = {get_name(), ".", "TxDiffDcaMode_p2_bits"};
      this.TxDiffDcaMode_p2.configure(this, null, "");
      this.TxDiffDcaMode_p2.build();
      this.default_map.add_reg(this.TxDiffDcaMode_p2, `UVM_REG_ADDR_WIDTH'h8D, "RW", 0);
		this.TxDiffDcaMode_p2_TxDiffDcaMode_p2 = this.TxDiffDcaMode_p2.TxDiffDcaMode_p2;
      this.RxDFETap1SelTg0Ln0_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln0_p2::type_id::create("RxDFETap1SelTg0Ln0_p2",,get_full_name());
      if(this.RxDFETap1SelTg0Ln0_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap1SelTg0Ln0_p2.cg_bits.option.name = {get_name(), ".", "RxDFETap1SelTg0Ln0_p2_bits"};
      this.RxDFETap1SelTg0Ln0_p2.configure(this, null, "");
      this.RxDFETap1SelTg0Ln0_p2.build();
      this.default_map.add_reg(this.RxDFETap1SelTg0Ln0_p2, `UVM_REG_ADDR_WIDTH'hA0, "RW", 0);
		this.RxDFETap1SelTg0Ln0_p2_RxDFETap1SelTg0Ln0_p2 = this.RxDFETap1SelTg0Ln0_p2.RxDFETap1SelTg0Ln0_p2;
      this.RxDFETap1SelTg1Ln0_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln0_p2::type_id::create("RxDFETap1SelTg1Ln0_p2",,get_full_name());
      if(this.RxDFETap1SelTg1Ln0_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap1SelTg1Ln0_p2.cg_bits.option.name = {get_name(), ".", "RxDFETap1SelTg1Ln0_p2_bits"};
      this.RxDFETap1SelTg1Ln0_p2.configure(this, null, "");
      this.RxDFETap1SelTg1Ln0_p2.build();
      this.default_map.add_reg(this.RxDFETap1SelTg1Ln0_p2, `UVM_REG_ADDR_WIDTH'hA1, "RW", 0);
		this.RxDFETap1SelTg1Ln0_p2_RxDFETap1SelTg1Ln0_p2 = this.RxDFETap1SelTg1Ln0_p2.RxDFETap1SelTg1Ln0_p2;
      this.RxDFETap2SelTg0Ln0_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln0_p2::type_id::create("RxDFETap2SelTg0Ln0_p2",,get_full_name());
      if(this.RxDFETap2SelTg0Ln0_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap2SelTg0Ln0_p2.cg_bits.option.name = {get_name(), ".", "RxDFETap2SelTg0Ln0_p2_bits"};
      this.RxDFETap2SelTg0Ln0_p2.configure(this, null, "");
      this.RxDFETap2SelTg0Ln0_p2.build();
      this.default_map.add_reg(this.RxDFETap2SelTg0Ln0_p2, `UVM_REG_ADDR_WIDTH'hA4, "RW", 0);
		this.RxDFETap2SelTg0Ln0_p2_RxDFETap2SelTg0Ln0_p2 = this.RxDFETap2SelTg0Ln0_p2.RxDFETap2SelTg0Ln0_p2;
      this.RxDFETap2SelTg1Ln0_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln0_p2::type_id::create("RxDFETap2SelTg1Ln0_p2",,get_full_name());
      if(this.RxDFETap2SelTg1Ln0_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap2SelTg1Ln0_p2.cg_bits.option.name = {get_name(), ".", "RxDFETap2SelTg1Ln0_p2_bits"};
      this.RxDFETap2SelTg1Ln0_p2.configure(this, null, "");
      this.RxDFETap2SelTg1Ln0_p2.build();
      this.default_map.add_reg(this.RxDFETap2SelTg1Ln0_p2, `UVM_REG_ADDR_WIDTH'hA5, "RW", 0);
		this.RxDFETap2SelTg1Ln0_p2_RxDFETap2SelTg1Ln0_p2 = this.RxDFETap2SelTg1Ln0_p2.RxDFETap2SelTg1Ln0_p2;
      this.RxDFETap1SelTg0Ln1_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln1_p2::type_id::create("RxDFETap1SelTg0Ln1_p2",,get_full_name());
      if(this.RxDFETap1SelTg0Ln1_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap1SelTg0Ln1_p2.cg_bits.option.name = {get_name(), ".", "RxDFETap1SelTg0Ln1_p2_bits"};
      this.RxDFETap1SelTg0Ln1_p2.configure(this, null, "");
      this.RxDFETap1SelTg0Ln1_p2.build();
      this.default_map.add_reg(this.RxDFETap1SelTg0Ln1_p2, `UVM_REG_ADDR_WIDTH'hB0, "RW", 0);
		this.RxDFETap1SelTg0Ln1_p2_RxDFETap1SelTg0Ln1_p2 = this.RxDFETap1SelTg0Ln1_p2.RxDFETap1SelTg0Ln1_p2;
      this.RxDFETap1SelTg1Ln1_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln1_p2::type_id::create("RxDFETap1SelTg1Ln1_p2",,get_full_name());
      if(this.RxDFETap1SelTg1Ln1_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap1SelTg1Ln1_p2.cg_bits.option.name = {get_name(), ".", "RxDFETap1SelTg1Ln1_p2_bits"};
      this.RxDFETap1SelTg1Ln1_p2.configure(this, null, "");
      this.RxDFETap1SelTg1Ln1_p2.build();
      this.default_map.add_reg(this.RxDFETap1SelTg1Ln1_p2, `UVM_REG_ADDR_WIDTH'hB1, "RW", 0);
		this.RxDFETap1SelTg1Ln1_p2_RxDFETap1SelTg1Ln1_p2 = this.RxDFETap1SelTg1Ln1_p2.RxDFETap1SelTg1Ln1_p2;
      this.RxDFETap2SelTg0Ln1_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln1_p2::type_id::create("RxDFETap2SelTg0Ln1_p2",,get_full_name());
      if(this.RxDFETap2SelTg0Ln1_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap2SelTg0Ln1_p2.cg_bits.option.name = {get_name(), ".", "RxDFETap2SelTg0Ln1_p2_bits"};
      this.RxDFETap2SelTg0Ln1_p2.configure(this, null, "");
      this.RxDFETap2SelTg0Ln1_p2.build();
      this.default_map.add_reg(this.RxDFETap2SelTg0Ln1_p2, `UVM_REG_ADDR_WIDTH'hB4, "RW", 0);
		this.RxDFETap2SelTg0Ln1_p2_RxDFETap2SelTg0Ln1_p2 = this.RxDFETap2SelTg0Ln1_p2.RxDFETap2SelTg0Ln1_p2;
      this.RxDFETap2SelTg1Ln1_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln1_p2::type_id::create("RxDFETap2SelTg1Ln1_p2",,get_full_name());
      if(this.RxDFETap2SelTg1Ln1_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap2SelTg1Ln1_p2.cg_bits.option.name = {get_name(), ".", "RxDFETap2SelTg1Ln1_p2_bits"};
      this.RxDFETap2SelTg1Ln1_p2.configure(this, null, "");
      this.RxDFETap2SelTg1Ln1_p2.build();
      this.default_map.add_reg(this.RxDFETap2SelTg1Ln1_p2, `UVM_REG_ADDR_WIDTH'hB5, "RW", 0);
		this.RxDFETap2SelTg1Ln1_p2_RxDFETap2SelTg1Ln1_p2 = this.RxDFETap2SelTg1Ln1_p2.RxDFETap2SelTg1Ln1_p2;
      this.RxDFETap1SelTg0Ln2_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln2_p2::type_id::create("RxDFETap1SelTg0Ln2_p2",,get_full_name());
      if(this.RxDFETap1SelTg0Ln2_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap1SelTg0Ln2_p2.cg_bits.option.name = {get_name(), ".", "RxDFETap1SelTg0Ln2_p2_bits"};
      this.RxDFETap1SelTg0Ln2_p2.configure(this, null, "");
      this.RxDFETap1SelTg0Ln2_p2.build();
      this.default_map.add_reg(this.RxDFETap1SelTg0Ln2_p2, `UVM_REG_ADDR_WIDTH'hC0, "RW", 0);
		this.RxDFETap1SelTg0Ln2_p2_RxDFETap1SelTg0Ln2_p2 = this.RxDFETap1SelTg0Ln2_p2.RxDFETap1SelTg0Ln2_p2;
      this.RxDFETap1SelTg1Ln2_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln2_p2::type_id::create("RxDFETap1SelTg1Ln2_p2",,get_full_name());
      if(this.RxDFETap1SelTg1Ln2_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap1SelTg1Ln2_p2.cg_bits.option.name = {get_name(), ".", "RxDFETap1SelTg1Ln2_p2_bits"};
      this.RxDFETap1SelTg1Ln2_p2.configure(this, null, "");
      this.RxDFETap1SelTg1Ln2_p2.build();
      this.default_map.add_reg(this.RxDFETap1SelTg1Ln2_p2, `UVM_REG_ADDR_WIDTH'hC1, "RW", 0);
		this.RxDFETap1SelTg1Ln2_p2_RxDFETap1SelTg1Ln2_p2 = this.RxDFETap1SelTg1Ln2_p2.RxDFETap1SelTg1Ln2_p2;
      this.RxDFETap2SelTg0Ln2_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln2_p2::type_id::create("RxDFETap2SelTg0Ln2_p2",,get_full_name());
      if(this.RxDFETap2SelTg0Ln2_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap2SelTg0Ln2_p2.cg_bits.option.name = {get_name(), ".", "RxDFETap2SelTg0Ln2_p2_bits"};
      this.RxDFETap2SelTg0Ln2_p2.configure(this, null, "");
      this.RxDFETap2SelTg0Ln2_p2.build();
      this.default_map.add_reg(this.RxDFETap2SelTg0Ln2_p2, `UVM_REG_ADDR_WIDTH'hC4, "RW", 0);
		this.RxDFETap2SelTg0Ln2_p2_RxDFETap2SelTg0Ln2_p2 = this.RxDFETap2SelTg0Ln2_p2.RxDFETap2SelTg0Ln2_p2;
      this.RxDFETap2SelTg1Ln2_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln2_p2::type_id::create("RxDFETap2SelTg1Ln2_p2",,get_full_name());
      if(this.RxDFETap2SelTg1Ln2_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap2SelTg1Ln2_p2.cg_bits.option.name = {get_name(), ".", "RxDFETap2SelTg1Ln2_p2_bits"};
      this.RxDFETap2SelTg1Ln2_p2.configure(this, null, "");
      this.RxDFETap2SelTg1Ln2_p2.build();
      this.default_map.add_reg(this.RxDFETap2SelTg1Ln2_p2, `UVM_REG_ADDR_WIDTH'hC5, "RW", 0);
		this.RxDFETap2SelTg1Ln2_p2_RxDFETap2SelTg1Ln2_p2 = this.RxDFETap2SelTg1Ln2_p2.RxDFETap2SelTg1Ln2_p2;
      this.RxDFETap1SelTg0Ln3_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg0Ln3_p2::type_id::create("RxDFETap1SelTg0Ln3_p2",,get_full_name());
      if(this.RxDFETap1SelTg0Ln3_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap1SelTg0Ln3_p2.cg_bits.option.name = {get_name(), ".", "RxDFETap1SelTg0Ln3_p2_bits"};
      this.RxDFETap1SelTg0Ln3_p2.configure(this, null, "");
      this.RxDFETap1SelTg0Ln3_p2.build();
      this.default_map.add_reg(this.RxDFETap1SelTg0Ln3_p2, `UVM_REG_ADDR_WIDTH'hD0, "RW", 0);
		this.RxDFETap1SelTg0Ln3_p2_RxDFETap1SelTg0Ln3_p2 = this.RxDFETap1SelTg0Ln3_p2.RxDFETap1SelTg0Ln3_p2;
      this.RxDFETap1SelTg1Ln3_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap1SelTg1Ln3_p2::type_id::create("RxDFETap1SelTg1Ln3_p2",,get_full_name());
      if(this.RxDFETap1SelTg1Ln3_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap1SelTg1Ln3_p2.cg_bits.option.name = {get_name(), ".", "RxDFETap1SelTg1Ln3_p2_bits"};
      this.RxDFETap1SelTg1Ln3_p2.configure(this, null, "");
      this.RxDFETap1SelTg1Ln3_p2.build();
      this.default_map.add_reg(this.RxDFETap1SelTg1Ln3_p2, `UVM_REG_ADDR_WIDTH'hD1, "RW", 0);
		this.RxDFETap1SelTg1Ln3_p2_RxDFETap1SelTg1Ln3_p2 = this.RxDFETap1SelTg1Ln3_p2.RxDFETap1SelTg1Ln3_p2;
      this.RxDFETap2SelTg0Ln3_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg0Ln3_p2::type_id::create("RxDFETap2SelTg0Ln3_p2",,get_full_name());
      if(this.RxDFETap2SelTg0Ln3_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap2SelTg0Ln3_p2.cg_bits.option.name = {get_name(), ".", "RxDFETap2SelTg0Ln3_p2_bits"};
      this.RxDFETap2SelTg0Ln3_p2.configure(this, null, "");
      this.RxDFETap2SelTg0Ln3_p2.build();
      this.default_map.add_reg(this.RxDFETap2SelTg0Ln3_p2, `UVM_REG_ADDR_WIDTH'hD4, "RW", 0);
		this.RxDFETap2SelTg0Ln3_p2_RxDFETap2SelTg0Ln3_p2 = this.RxDFETap2SelTg0Ln3_p2.RxDFETap2SelTg0Ln3_p2;
      this.RxDFETap2SelTg1Ln3_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDFETap2SelTg1Ln3_p2::type_id::create("RxDFETap2SelTg1Ln3_p2",,get_full_name());
      if(this.RxDFETap2SelTg1Ln3_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDFETap2SelTg1Ln3_p2.cg_bits.option.name = {get_name(), ".", "RxDFETap2SelTg1Ln3_p2_bits"};
      this.RxDFETap2SelTg1Ln3_p2.configure(this, null, "");
      this.RxDFETap2SelTg1Ln3_p2.build();
      this.default_map.add_reg(this.RxDFETap2SelTg1Ln3_p2, `UVM_REG_ADDR_WIDTH'hD5, "RW", 0);
		this.RxDFETap2SelTg1Ln3_p2_RxDFETap2SelTg1Ln3_p2 = this.RxDFETap2SelTg1Ln3_p2.RxDFETap2SelTg1Ln3_p2;
      this.PclkDCACodeDqLn0_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn0_p2::type_id::create("PclkDCACodeDqLn0_p2",,get_full_name());
      if(this.PclkDCACodeDqLn0_p2.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACodeDqLn0_p2.cg_bits.option.name = {get_name(), ".", "PclkDCACodeDqLn0_p2_bits"};
      this.PclkDCACodeDqLn0_p2.configure(this, null, "");
      this.PclkDCACodeDqLn0_p2.build();
      this.default_map.add_reg(this.PclkDCACodeDqLn0_p2, `UVM_REG_ADDR_WIDTH'hF0, "RW", 0);
		this.PclkDCACodeDqLn0_p2_PclkDCACoarseDqLn0 = this.PclkDCACodeDqLn0_p2.PclkDCACoarseDqLn0;
		this.PclkDCACoarseDqLn0 = this.PclkDCACodeDqLn0_p2.PclkDCACoarseDqLn0;
		this.PclkDCACodeDqLn0_p2_PclkDCAFineDqLn0 = this.PclkDCACodeDqLn0_p2.PclkDCAFineDqLn0;
		this.PclkDCAFineDqLn0 = this.PclkDCACodeDqLn0_p2.PclkDCAFineDqLn0;
      this.PclkDCACodeDqLn1_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn1_p2::type_id::create("PclkDCACodeDqLn1_p2",,get_full_name());
      if(this.PclkDCACodeDqLn1_p2.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACodeDqLn1_p2.cg_bits.option.name = {get_name(), ".", "PclkDCACodeDqLn1_p2_bits"};
      this.PclkDCACodeDqLn1_p2.configure(this, null, "");
      this.PclkDCACodeDqLn1_p2.build();
      this.default_map.add_reg(this.PclkDCACodeDqLn1_p2, `UVM_REG_ADDR_WIDTH'hF1, "RW", 0);
		this.PclkDCACodeDqLn1_p2_PclkDCACoarseDqLn1 = this.PclkDCACodeDqLn1_p2.PclkDCACoarseDqLn1;
		this.PclkDCACoarseDqLn1 = this.PclkDCACodeDqLn1_p2.PclkDCACoarseDqLn1;
		this.PclkDCACodeDqLn1_p2_PclkDCAFineDqLn1 = this.PclkDCACodeDqLn1_p2.PclkDCAFineDqLn1;
		this.PclkDCAFineDqLn1 = this.PclkDCACodeDqLn1_p2.PclkDCAFineDqLn1;
      this.PclkDCACodeDqLn2_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn2_p2::type_id::create("PclkDCACodeDqLn2_p2",,get_full_name());
      if(this.PclkDCACodeDqLn2_p2.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACodeDqLn2_p2.cg_bits.option.name = {get_name(), ".", "PclkDCACodeDqLn2_p2_bits"};
      this.PclkDCACodeDqLn2_p2.configure(this, null, "");
      this.PclkDCACodeDqLn2_p2.build();
      this.default_map.add_reg(this.PclkDCACodeDqLn2_p2, `UVM_REG_ADDR_WIDTH'hF2, "RW", 0);
		this.PclkDCACodeDqLn2_p2_PclkDCACoarseDqLn2 = this.PclkDCACodeDqLn2_p2.PclkDCACoarseDqLn2;
		this.PclkDCACoarseDqLn2 = this.PclkDCACodeDqLn2_p2.PclkDCACoarseDqLn2;
		this.PclkDCACodeDqLn2_p2_PclkDCAFineDqLn2 = this.PclkDCACodeDqLn2_p2.PclkDCAFineDqLn2;
		this.PclkDCAFineDqLn2 = this.PclkDCACodeDqLn2_p2.PclkDCAFineDqLn2;
      this.PclkDCACodeDqLn3_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDqLn3_p2::type_id::create("PclkDCACodeDqLn3_p2",,get_full_name());
      if(this.PclkDCACodeDqLn3_p2.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACodeDqLn3_p2.cg_bits.option.name = {get_name(), ".", "PclkDCACodeDqLn3_p2_bits"};
      this.PclkDCACodeDqLn3_p2.configure(this, null, "");
      this.PclkDCACodeDqLn3_p2.build();
      this.default_map.add_reg(this.PclkDCACodeDqLn3_p2, `UVM_REG_ADDR_WIDTH'hF3, "RW", 0);
		this.PclkDCACodeDqLn3_p2_PclkDCACoarseDqLn3 = this.PclkDCACodeDqLn3_p2.PclkDCACoarseDqLn3;
		this.PclkDCACoarseDqLn3 = this.PclkDCACodeDqLn3_p2.PclkDCACoarseDqLn3;
		this.PclkDCACodeDqLn3_p2_PclkDCAFineDqLn3 = this.PclkDCACodeDqLn3_p2.PclkDCAFineDqLn3;
		this.PclkDCAFineDqLn3 = this.PclkDCACodeDqLn3_p2.PclkDCAFineDqLn3;
      this.PclkDCACodeDQS_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCACodeDQS_p2::type_id::create("PclkDCACodeDQS_p2",,get_full_name());
      if(this.PclkDCACodeDQS_p2.has_coverage(UVM_CVR_ALL))
      	this.PclkDCACodeDQS_p2.cg_bits.option.name = {get_name(), ".", "PclkDCACodeDQS_p2_bits"};
      this.PclkDCACodeDQS_p2.configure(this, null, "");
      this.PclkDCACodeDQS_p2.build();
      this.default_map.add_reg(this.PclkDCACodeDQS_p2, `UVM_REG_ADDR_WIDTH'hF5, "RW", 0);
		this.PclkDCACodeDQS_p2_PclkDCACoarseDQS = this.PclkDCACodeDQS_p2.PclkDCACoarseDQS;
		this.PclkDCACoarseDQS = this.PclkDCACodeDQS_p2.PclkDCACoarseDQS;
		this.PclkDCACodeDQS_p2_PclkDCAFineDQS = this.PclkDCACodeDQS_p2.PclkDCAFineDQS;
		this.PclkDCAFineDQS = this.PclkDCACodeDQS_p2.PclkDCAFineDQS;
      this.HMReservedP1_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_HMReservedP1_p2::type_id::create("HMReservedP1_p2",,get_full_name());
      if(this.HMReservedP1_p2.has_coverage(UVM_CVR_ALL))
      	this.HMReservedP1_p2.cg_bits.option.name = {get_name(), ".", "HMReservedP1_p2_bits"};
      this.HMReservedP1_p2.configure(this, null, "");
      this.HMReservedP1_p2.build();
      this.default_map.add_reg(this.HMReservedP1_p2, `UVM_REG_ADDR_WIDTH'hFF, "RW", 0);
		this.HMReservedP1_p2_HMReservedP1_p2 = this.HMReservedP1_p2.HMReservedP1_p2;
      this.PclkDCATxLcdlPhase_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCATxLcdlPhase_p2::type_id::create("PclkDCATxLcdlPhase_p2",,get_full_name());
      if(this.PclkDCATxLcdlPhase_p2.has_coverage(UVM_CVR_ALL))
      	this.PclkDCATxLcdlPhase_p2.cg_bits.option.name = {get_name(), ".", "PclkDCATxLcdlPhase_p2_bits"};
      this.PclkDCATxLcdlPhase_p2.configure(this, null, "");
      this.PclkDCATxLcdlPhase_p2.build();
      this.default_map.add_reg(this.PclkDCATxLcdlPhase_p2, `UVM_REG_ADDR_WIDTH'h110, "RW", 0);
		this.PclkDCATxLcdlPhase_p2_PclkDCATxLcdlPhase_p2 = this.PclkDCATxLcdlPhase_p2.PclkDCATxLcdlPhase_p2;
      this.PclkDCDOffsetDqLn0_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn0_p2::type_id::create("PclkDCDOffsetDqLn0_p2",,get_full_name());
      if(this.PclkDCDOffsetDqLn0_p2.has_coverage(UVM_CVR_ALL))
      	this.PclkDCDOffsetDqLn0_p2.cg_bits.option.name = {get_name(), ".", "PclkDCDOffsetDqLn0_p2_bits"};
      this.PclkDCDOffsetDqLn0_p2.configure(this, null, "");
      this.PclkDCDOffsetDqLn0_p2.build();
      this.default_map.add_reg(this.PclkDCDOffsetDqLn0_p2, `UVM_REG_ADDR_WIDTH'h200, "RW", 0);
		this.PclkDCDOffsetDqLn0_p2_PclkDCDOffsetDqLn0_p2 = this.PclkDCDOffsetDqLn0_p2.PclkDCDOffsetDqLn0_p2;
      this.PclkDCDOffsetDqLn1_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn1_p2::type_id::create("PclkDCDOffsetDqLn1_p2",,get_full_name());
      if(this.PclkDCDOffsetDqLn1_p2.has_coverage(UVM_CVR_ALL))
      	this.PclkDCDOffsetDqLn1_p2.cg_bits.option.name = {get_name(), ".", "PclkDCDOffsetDqLn1_p2_bits"};
      this.PclkDCDOffsetDqLn1_p2.configure(this, null, "");
      this.PclkDCDOffsetDqLn1_p2.build();
      this.default_map.add_reg(this.PclkDCDOffsetDqLn1_p2, `UVM_REG_ADDR_WIDTH'h201, "RW", 0);
		this.PclkDCDOffsetDqLn1_p2_PclkDCDOffsetDqLn1_p2 = this.PclkDCDOffsetDqLn1_p2.PclkDCDOffsetDqLn1_p2;
      this.PclkDCDOffsetDqLn2_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn2_p2::type_id::create("PclkDCDOffsetDqLn2_p2",,get_full_name());
      if(this.PclkDCDOffsetDqLn2_p2.has_coverage(UVM_CVR_ALL))
      	this.PclkDCDOffsetDqLn2_p2.cg_bits.option.name = {get_name(), ".", "PclkDCDOffsetDqLn2_p2_bits"};
      this.PclkDCDOffsetDqLn2_p2.configure(this, null, "");
      this.PclkDCDOffsetDqLn2_p2.build();
      this.default_map.add_reg(this.PclkDCDOffsetDqLn2_p2, `UVM_REG_ADDR_WIDTH'h202, "RW", 0);
		this.PclkDCDOffsetDqLn2_p2_PclkDCDOffsetDqLn2_p2 = this.PclkDCDOffsetDqLn2_p2.PclkDCDOffsetDqLn2_p2;
      this.PclkDCDOffsetDqLn3_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDqLn3_p2::type_id::create("PclkDCDOffsetDqLn3_p2",,get_full_name());
      if(this.PclkDCDOffsetDqLn3_p2.has_coverage(UVM_CVR_ALL))
      	this.PclkDCDOffsetDqLn3_p2.cg_bits.option.name = {get_name(), ".", "PclkDCDOffsetDqLn3_p2_bits"};
      this.PclkDCDOffsetDqLn3_p2.configure(this, null, "");
      this.PclkDCDOffsetDqLn3_p2.build();
      this.default_map.add_reg(this.PclkDCDOffsetDqLn3_p2, `UVM_REG_ADDR_WIDTH'h203, "RW", 0);
		this.PclkDCDOffsetDqLn3_p2_PclkDCDOffsetDqLn3_p2 = this.PclkDCDOffsetDqLn3_p2.PclkDCDOffsetDqLn3_p2;
      this.PclkDCDOffsetDQS_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCDOffsetDQS_p2::type_id::create("PclkDCDOffsetDQS_p2",,get_full_name());
      if(this.PclkDCDOffsetDQS_p2.has_coverage(UVM_CVR_ALL))
      	this.PclkDCDOffsetDQS_p2.cg_bits.option.name = {get_name(), ".", "PclkDCDOffsetDQS_p2_bits"};
      this.PclkDCDOffsetDQS_p2.configure(this, null, "");
      this.PclkDCDOffsetDQS_p2.build();
      this.default_map.add_reg(this.PclkDCDOffsetDQS_p2, `UVM_REG_ADDR_WIDTH'h205, "RW", 0);
		this.PclkDCDOffsetDQS_p2_PclkDCDOffsetDQS_p2 = this.PclkDCDOffsetDQS_p2.PclkDCDOffsetDQS_p2;
      this.TxDcaCtrlTTg0_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTTg0_p2::type_id::create("TxDcaCtrlTTg0_p2",,get_full_name());
      if(this.TxDcaCtrlTTg0_p2.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlTTg0_p2.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlTTg0_p2_bits"};
      this.TxDcaCtrlTTg0_p2.configure(this, null, "");
      this.TxDcaCtrlTTg0_p2.build();
      this.default_map.add_reg(this.TxDcaCtrlTTg0_p2, `UVM_REG_ADDR_WIDTH'h550, "RW", 0);
		this.TxDcaCtrlTTg0_p2_TxDcaFinePDTTg0 = this.TxDcaCtrlTTg0_p2.TxDcaFinePDTTg0;
		this.TxDcaFinePDTTg0 = this.TxDcaCtrlTTg0_p2.TxDcaFinePDTTg0;
		this.TxDcaCtrlTTg0_p2_TxDcaFinePUTTg0 = this.TxDcaCtrlTTg0_p2.TxDcaFinePUTTg0;
		this.TxDcaFinePUTTg0 = this.TxDcaCtrlTTg0_p2.TxDcaFinePUTTg0;
		this.TxDcaCtrlTTg0_p2_TxDcaCoarseTTg0 = this.TxDcaCtrlTTg0_p2.TxDcaCoarseTTg0;
		this.TxDcaCoarseTTg0 = this.TxDcaCtrlTTg0_p2.TxDcaCoarseTTg0;
      this.TxDcaCtrlTTg1_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTTg1_p2::type_id::create("TxDcaCtrlTTg1_p2",,get_full_name());
      if(this.TxDcaCtrlTTg1_p2.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlTTg1_p2.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlTTg1_p2_bits"};
      this.TxDcaCtrlTTg1_p2.configure(this, null, "");
      this.TxDcaCtrlTTg1_p2.build();
      this.default_map.add_reg(this.TxDcaCtrlTTg1_p2, `UVM_REG_ADDR_WIDTH'h551, "RW", 0);
		this.TxDcaCtrlTTg1_p2_TxDcaFinePDTTg1 = this.TxDcaCtrlTTg1_p2.TxDcaFinePDTTg1;
		this.TxDcaFinePDTTg1 = this.TxDcaCtrlTTg1_p2.TxDcaFinePDTTg1;
		this.TxDcaCtrlTTg1_p2_TxDcaFinePUTTg1 = this.TxDcaCtrlTTg1_p2.TxDcaFinePUTTg1;
		this.TxDcaFinePUTTg1 = this.TxDcaCtrlTTg1_p2.TxDcaFinePUTTg1;
		this.TxDcaCtrlTTg1_p2_TxDcaCoarseTTg1 = this.TxDcaCtrlTTg1_p2.TxDcaCoarseTTg1;
		this.TxDcaCoarseTTg1 = this.TxDcaCtrlTTg1_p2.TxDcaCoarseTTg1;
      this.TxDcaCtrlCTg0_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlCTg0_p2::type_id::create("TxDcaCtrlCTg0_p2",,get_full_name());
      if(this.TxDcaCtrlCTg0_p2.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlCTg0_p2.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlCTg0_p2_bits"};
      this.TxDcaCtrlCTg0_p2.configure(this, null, "");
      this.TxDcaCtrlCTg0_p2.build();
      this.default_map.add_reg(this.TxDcaCtrlCTg0_p2, `UVM_REG_ADDR_WIDTH'h560, "RW", 0);
		this.TxDcaCtrlCTg0_p2_TxDcaFinePDCTg0 = this.TxDcaCtrlCTg0_p2.TxDcaFinePDCTg0;
		this.TxDcaFinePDCTg0 = this.TxDcaCtrlCTg0_p2.TxDcaFinePDCTg0;
		this.TxDcaCtrlCTg0_p2_TxDcaFinePUCTg0 = this.TxDcaCtrlCTg0_p2.TxDcaFinePUCTg0;
		this.TxDcaFinePUCTg0 = this.TxDcaCtrlCTg0_p2.TxDcaFinePUCTg0;
		this.TxDcaCtrlCTg0_p2_TxDcaCoarseCTg0 = this.TxDcaCtrlCTg0_p2.TxDcaCoarseCTg0;
		this.TxDcaCoarseCTg0 = this.TxDcaCtrlCTg0_p2.TxDcaCoarseCTg0;
      this.TxDcaCtrlCTg1_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlCTg1_p2::type_id::create("TxDcaCtrlCTg1_p2",,get_full_name());
      if(this.TxDcaCtrlCTg1_p2.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlCTg1_p2.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlCTg1_p2_bits"};
      this.TxDcaCtrlCTg1_p2.configure(this, null, "");
      this.TxDcaCtrlCTg1_p2.build();
      this.default_map.add_reg(this.TxDcaCtrlCTg1_p2, `UVM_REG_ADDR_WIDTH'h561, "RW", 0);
		this.TxDcaCtrlCTg1_p2_TxDcaFinePDCTg1 = this.TxDcaCtrlCTg1_p2.TxDcaFinePDCTg1;
		this.TxDcaFinePDCTg1 = this.TxDcaCtrlCTg1_p2.TxDcaFinePDCTg1;
		this.TxDcaCtrlCTg1_p2_TxDcaFinePUCTg1 = this.TxDcaCtrlCTg1_p2.TxDcaFinePUCTg1;
		this.TxDcaFinePUCTg1 = this.TxDcaCtrlCTg1_p2.TxDcaFinePUCTg1;
		this.TxDcaCtrlCTg1_p2_TxDcaCoarseCTg1 = this.TxDcaCtrlCTg1_p2.TxDcaCoarseCTg1;
		this.TxDcaCoarseCTg1 = this.TxDcaCtrlCTg1_p2.TxDcaCoarseCTg1;
      this.RxDcaCtrlTTg0_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlTTg0_p2::type_id::create("RxDcaCtrlTTg0_p2",,get_full_name());
      if(this.RxDcaCtrlTTg0_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDcaCtrlTTg0_p2.cg_bits.option.name = {get_name(), ".", "RxDcaCtrlTTg0_p2_bits"};
      this.RxDcaCtrlTTg0_p2.configure(this, null, "");
      this.RxDcaCtrlTTg0_p2.build();
      this.default_map.add_reg(this.RxDcaCtrlTTg0_p2, `UVM_REG_ADDR_WIDTH'h570, "RW", 0);
		this.RxDcaCtrlTTg0_p2_RxDcaFinePDTTg0 = this.RxDcaCtrlTTg0_p2.RxDcaFinePDTTg0;
		this.RxDcaFinePDTTg0 = this.RxDcaCtrlTTg0_p2.RxDcaFinePDTTg0;
		this.RxDcaCtrlTTg0_p2_RxDcaFinePUTTg0 = this.RxDcaCtrlTTg0_p2.RxDcaFinePUTTg0;
		this.RxDcaFinePUTTg0 = this.RxDcaCtrlTTg0_p2.RxDcaFinePUTTg0;
		this.RxDcaCtrlTTg0_p2_RxDcaCoarseTTg0 = this.RxDcaCtrlTTg0_p2.RxDcaCoarseTTg0;
		this.RxDcaCoarseTTg0 = this.RxDcaCtrlTTg0_p2.RxDcaCoarseTTg0;
      this.RxDcaCtrlTTg1_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlTTg1_p2::type_id::create("RxDcaCtrlTTg1_p2",,get_full_name());
      if(this.RxDcaCtrlTTg1_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDcaCtrlTTg1_p2.cg_bits.option.name = {get_name(), ".", "RxDcaCtrlTTg1_p2_bits"};
      this.RxDcaCtrlTTg1_p2.configure(this, null, "");
      this.RxDcaCtrlTTg1_p2.build();
      this.default_map.add_reg(this.RxDcaCtrlTTg1_p2, `UVM_REG_ADDR_WIDTH'h571, "RW", 0);
		this.RxDcaCtrlTTg1_p2_RxDcaFinePDTTg1 = this.RxDcaCtrlTTg1_p2.RxDcaFinePDTTg1;
		this.RxDcaFinePDTTg1 = this.RxDcaCtrlTTg1_p2.RxDcaFinePDTTg1;
		this.RxDcaCtrlTTg1_p2_RxDcaFinePUTTg1 = this.RxDcaCtrlTTg1_p2.RxDcaFinePUTTg1;
		this.RxDcaFinePUTTg1 = this.RxDcaCtrlTTg1_p2.RxDcaFinePUTTg1;
		this.RxDcaCtrlTTg1_p2_RxDcaCoarseTTg1 = this.RxDcaCtrlTTg1_p2.RxDcaCoarseTTg1;
		this.RxDcaCoarseTTg1 = this.RxDcaCtrlTTg1_p2.RxDcaCoarseTTg1;
      this.RxDcaCtrlCTg0_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlCTg0_p2::type_id::create("RxDcaCtrlCTg0_p2",,get_full_name());
      if(this.RxDcaCtrlCTg0_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDcaCtrlCTg0_p2.cg_bits.option.name = {get_name(), ".", "RxDcaCtrlCTg0_p2_bits"};
      this.RxDcaCtrlCTg0_p2.configure(this, null, "");
      this.RxDcaCtrlCTg0_p2.build();
      this.default_map.add_reg(this.RxDcaCtrlCTg0_p2, `UVM_REG_ADDR_WIDTH'h580, "RW", 0);
		this.RxDcaCtrlCTg0_p2_RxDcaFinePDCTg0 = this.RxDcaCtrlCTg0_p2.RxDcaFinePDCTg0;
		this.RxDcaFinePDCTg0 = this.RxDcaCtrlCTg0_p2.RxDcaFinePDCTg0;
		this.RxDcaCtrlCTg0_p2_RxDcaFinePUCTg0 = this.RxDcaCtrlCTg0_p2.RxDcaFinePUCTg0;
		this.RxDcaFinePUCTg0 = this.RxDcaCtrlCTg0_p2.RxDcaFinePUCTg0;
		this.RxDcaCtrlCTg0_p2_RxDcaCoarseCTg0 = this.RxDcaCtrlCTg0_p2.RxDcaCoarseCTg0;
		this.RxDcaCoarseCTg0 = this.RxDcaCtrlCTg0_p2.RxDcaCoarseCTg0;
      this.RxDcaCtrlCTg1_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_RxDcaCtrlCTg1_p2::type_id::create("RxDcaCtrlCTg1_p2",,get_full_name());
      if(this.RxDcaCtrlCTg1_p2.has_coverage(UVM_CVR_ALL))
      	this.RxDcaCtrlCTg1_p2.cg_bits.option.name = {get_name(), ".", "RxDcaCtrlCTg1_p2_bits"};
      this.RxDcaCtrlCTg1_p2.configure(this, null, "");
      this.RxDcaCtrlCTg1_p2.build();
      this.default_map.add_reg(this.RxDcaCtrlCTg1_p2, `UVM_REG_ADDR_WIDTH'h581, "RW", 0);
		this.RxDcaCtrlCTg1_p2_RxDcaFinePDCTg1 = this.RxDcaCtrlCTg1_p2.RxDcaFinePDCTg1;
		this.RxDcaFinePDCTg1 = this.RxDcaCtrlCTg1_p2.RxDcaFinePDCTg1;
		this.RxDcaCtrlCTg1_p2_RxDcaFinePUCTg1 = this.RxDcaCtrlCTg1_p2.RxDcaFinePUCTg1;
		this.RxDcaFinePUCTg1 = this.RxDcaCtrlCTg1_p2.RxDcaFinePUCTg1;
		this.RxDcaCtrlCTg1_p2_RxDcaCoarseCTg1 = this.RxDcaCtrlCTg1_p2.RxDcaCoarseCTg1;
		this.RxDcaCoarseCTg1 = this.RxDcaCtrlCTg1_p2.RxDcaCoarseCTg1;
      this.PclkDCALcdlAddDlySampEn_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_PclkDCALcdlAddDlySampEn_p2::type_id::create("PclkDCALcdlAddDlySampEn_p2",,get_full_name());
      if(this.PclkDCALcdlAddDlySampEn_p2.has_coverage(UVM_CVR_ALL))
      	this.PclkDCALcdlAddDlySampEn_p2.cg_bits.option.name = {get_name(), ".", "PclkDCALcdlAddDlySampEn_p2_bits"};
      this.PclkDCALcdlAddDlySampEn_p2.configure(this, null, "");
      this.PclkDCALcdlAddDlySampEn_p2.build();
      this.default_map.add_reg(this.PclkDCALcdlAddDlySampEn_p2, `UVM_REG_ADDR_WIDTH'h5E3, "RW", 0);
		this.PclkDCALcdlAddDlySampEn_p2_PclkDCALcdlAddDlySampEn_p2 = this.PclkDCALcdlAddDlySampEn_p2.PclkDCALcdlAddDlySampEn_p2;
      this.TxDcaCtrlTg0Ln0_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln0_p2::type_id::create("TxDcaCtrlTg0Ln0_p2",,get_full_name());
      if(this.TxDcaCtrlTg0Ln0_p2.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlTg0Ln0_p2.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlTg0Ln0_p2_bits"};
      this.TxDcaCtrlTg0Ln0_p2.configure(this, null, "");
      this.TxDcaCtrlTg0Ln0_p2.build();
      this.default_map.add_reg(this.TxDcaCtrlTg0Ln0_p2, `UVM_REG_ADDR_WIDTH'h600, "RW", 0);
		this.TxDcaCtrlTg0Ln0_p2_TxDcaCoarseTg0Ln0 = this.TxDcaCtrlTg0Ln0_p2.TxDcaCoarseTg0Ln0;
		this.TxDcaCoarseTg0Ln0 = this.TxDcaCtrlTg0Ln0_p2.TxDcaCoarseTg0Ln0;
		this.TxDcaCtrlTg0Ln0_p2_TxDcaFinePUTg0Ln0 = this.TxDcaCtrlTg0Ln0_p2.TxDcaFinePUTg0Ln0;
		this.TxDcaFinePUTg0Ln0 = this.TxDcaCtrlTg0Ln0_p2.TxDcaFinePUTg0Ln0;
		this.TxDcaCtrlTg0Ln0_p2_TxDcaFinePDTg0Ln0 = this.TxDcaCtrlTg0Ln0_p2.TxDcaFinePDTg0Ln0;
		this.TxDcaFinePDTg0Ln0 = this.TxDcaCtrlTg0Ln0_p2.TxDcaFinePDTg0Ln0;
      this.TxDcaCtrlTg1Ln0_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln0_p2::type_id::create("TxDcaCtrlTg1Ln0_p2",,get_full_name());
      if(this.TxDcaCtrlTg1Ln0_p2.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlTg1Ln0_p2.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlTg1Ln0_p2_bits"};
      this.TxDcaCtrlTg1Ln0_p2.configure(this, null, "");
      this.TxDcaCtrlTg1Ln0_p2.build();
      this.default_map.add_reg(this.TxDcaCtrlTg1Ln0_p2, `UVM_REG_ADDR_WIDTH'h601, "RW", 0);
		this.TxDcaCtrlTg1Ln0_p2_TxDcaCoarseTg1Ln0 = this.TxDcaCtrlTg1Ln0_p2.TxDcaCoarseTg1Ln0;
		this.TxDcaCoarseTg1Ln0 = this.TxDcaCtrlTg1Ln0_p2.TxDcaCoarseTg1Ln0;
		this.TxDcaCtrlTg1Ln0_p2_TxDcaFinePUTg1Ln0 = this.TxDcaCtrlTg1Ln0_p2.TxDcaFinePUTg1Ln0;
		this.TxDcaFinePUTg1Ln0 = this.TxDcaCtrlTg1Ln0_p2.TxDcaFinePUTg1Ln0;
		this.TxDcaCtrlTg1Ln0_p2_TxDcaFinePDTg1Ln0 = this.TxDcaCtrlTg1Ln0_p2.TxDcaFinePDTg1Ln0;
		this.TxDcaFinePDTg1Ln0 = this.TxDcaCtrlTg1Ln0_p2.TxDcaFinePDTg1Ln0;
      this.TxDcaCtrlTg0Ln1_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln1_p2::type_id::create("TxDcaCtrlTg0Ln1_p2",,get_full_name());
      if(this.TxDcaCtrlTg0Ln1_p2.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlTg0Ln1_p2.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlTg0Ln1_p2_bits"};
      this.TxDcaCtrlTg0Ln1_p2.configure(this, null, "");
      this.TxDcaCtrlTg0Ln1_p2.build();
      this.default_map.add_reg(this.TxDcaCtrlTg0Ln1_p2, `UVM_REG_ADDR_WIDTH'h610, "RW", 0);
		this.TxDcaCtrlTg0Ln1_p2_TxDcaCoarseTg0Ln1 = this.TxDcaCtrlTg0Ln1_p2.TxDcaCoarseTg0Ln1;
		this.TxDcaCoarseTg0Ln1 = this.TxDcaCtrlTg0Ln1_p2.TxDcaCoarseTg0Ln1;
		this.TxDcaCtrlTg0Ln1_p2_TxDcaFinePUTg0Ln1 = this.TxDcaCtrlTg0Ln1_p2.TxDcaFinePUTg0Ln1;
		this.TxDcaFinePUTg0Ln1 = this.TxDcaCtrlTg0Ln1_p2.TxDcaFinePUTg0Ln1;
		this.TxDcaCtrlTg0Ln1_p2_TxDcaFinePDTg0Ln1 = this.TxDcaCtrlTg0Ln1_p2.TxDcaFinePDTg0Ln1;
		this.TxDcaFinePDTg0Ln1 = this.TxDcaCtrlTg0Ln1_p2.TxDcaFinePDTg0Ln1;
      this.TxDcaCtrlTg1Ln1_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln1_p2::type_id::create("TxDcaCtrlTg1Ln1_p2",,get_full_name());
      if(this.TxDcaCtrlTg1Ln1_p2.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlTg1Ln1_p2.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlTg1Ln1_p2_bits"};
      this.TxDcaCtrlTg1Ln1_p2.configure(this, null, "");
      this.TxDcaCtrlTg1Ln1_p2.build();
      this.default_map.add_reg(this.TxDcaCtrlTg1Ln1_p2, `UVM_REG_ADDR_WIDTH'h611, "RW", 0);
		this.TxDcaCtrlTg1Ln1_p2_TxDcaCoarseTg1Ln1 = this.TxDcaCtrlTg1Ln1_p2.TxDcaCoarseTg1Ln1;
		this.TxDcaCoarseTg1Ln1 = this.TxDcaCtrlTg1Ln1_p2.TxDcaCoarseTg1Ln1;
		this.TxDcaCtrlTg1Ln1_p2_TxDcaFinePUTg1Ln1 = this.TxDcaCtrlTg1Ln1_p2.TxDcaFinePUTg1Ln1;
		this.TxDcaFinePUTg1Ln1 = this.TxDcaCtrlTg1Ln1_p2.TxDcaFinePUTg1Ln1;
		this.TxDcaCtrlTg1Ln1_p2_TxDcaFinePDTg1Ln1 = this.TxDcaCtrlTg1Ln1_p2.TxDcaFinePDTg1Ln1;
		this.TxDcaFinePDTg1Ln1 = this.TxDcaCtrlTg1Ln1_p2.TxDcaFinePDTg1Ln1;
      this.TxDcaCtrlTg0Ln2_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln2_p2::type_id::create("TxDcaCtrlTg0Ln2_p2",,get_full_name());
      if(this.TxDcaCtrlTg0Ln2_p2.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlTg0Ln2_p2.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlTg0Ln2_p2_bits"};
      this.TxDcaCtrlTg0Ln2_p2.configure(this, null, "");
      this.TxDcaCtrlTg0Ln2_p2.build();
      this.default_map.add_reg(this.TxDcaCtrlTg0Ln2_p2, `UVM_REG_ADDR_WIDTH'h620, "RW", 0);
		this.TxDcaCtrlTg0Ln2_p2_TxDcaCoarseTg0Ln2 = this.TxDcaCtrlTg0Ln2_p2.TxDcaCoarseTg0Ln2;
		this.TxDcaCoarseTg0Ln2 = this.TxDcaCtrlTg0Ln2_p2.TxDcaCoarseTg0Ln2;
		this.TxDcaCtrlTg0Ln2_p2_TxDcaFinePUTg0Ln2 = this.TxDcaCtrlTg0Ln2_p2.TxDcaFinePUTg0Ln2;
		this.TxDcaFinePUTg0Ln2 = this.TxDcaCtrlTg0Ln2_p2.TxDcaFinePUTg0Ln2;
		this.TxDcaCtrlTg0Ln2_p2_TxDcaFinePDTg0Ln2 = this.TxDcaCtrlTg0Ln2_p2.TxDcaFinePDTg0Ln2;
		this.TxDcaFinePDTg0Ln2 = this.TxDcaCtrlTg0Ln2_p2.TxDcaFinePDTg0Ln2;
      this.TxDcaCtrlTg1Ln2_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln2_p2::type_id::create("TxDcaCtrlTg1Ln2_p2",,get_full_name());
      if(this.TxDcaCtrlTg1Ln2_p2.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlTg1Ln2_p2.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlTg1Ln2_p2_bits"};
      this.TxDcaCtrlTg1Ln2_p2.configure(this, null, "");
      this.TxDcaCtrlTg1Ln2_p2.build();
      this.default_map.add_reg(this.TxDcaCtrlTg1Ln2_p2, `UVM_REG_ADDR_WIDTH'h621, "RW", 0);
		this.TxDcaCtrlTg1Ln2_p2_TxDcaCoarseTg1Ln2 = this.TxDcaCtrlTg1Ln2_p2.TxDcaCoarseTg1Ln2;
		this.TxDcaCoarseTg1Ln2 = this.TxDcaCtrlTg1Ln2_p2.TxDcaCoarseTg1Ln2;
		this.TxDcaCtrlTg1Ln2_p2_TxDcaFinePUTg1Ln2 = this.TxDcaCtrlTg1Ln2_p2.TxDcaFinePUTg1Ln2;
		this.TxDcaFinePUTg1Ln2 = this.TxDcaCtrlTg1Ln2_p2.TxDcaFinePUTg1Ln2;
		this.TxDcaCtrlTg1Ln2_p2_TxDcaFinePDTg1Ln2 = this.TxDcaCtrlTg1Ln2_p2.TxDcaFinePDTg1Ln2;
		this.TxDcaFinePDTg1Ln2 = this.TxDcaCtrlTg1Ln2_p2.TxDcaFinePDTg1Ln2;
      this.TxDcaCtrlTg0Ln3_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg0Ln3_p2::type_id::create("TxDcaCtrlTg0Ln3_p2",,get_full_name());
      if(this.TxDcaCtrlTg0Ln3_p2.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlTg0Ln3_p2.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlTg0Ln3_p2_bits"};
      this.TxDcaCtrlTg0Ln3_p2.configure(this, null, "");
      this.TxDcaCtrlTg0Ln3_p2.build();
      this.default_map.add_reg(this.TxDcaCtrlTg0Ln3_p2, `UVM_REG_ADDR_WIDTH'h630, "RW", 0);
		this.TxDcaCtrlTg0Ln3_p2_TxDcaCoarseTg0Ln3 = this.TxDcaCtrlTg0Ln3_p2.TxDcaCoarseTg0Ln3;
		this.TxDcaCoarseTg0Ln3 = this.TxDcaCtrlTg0Ln3_p2.TxDcaCoarseTg0Ln3;
		this.TxDcaCtrlTg0Ln3_p2_TxDcaFinePUTg0Ln3 = this.TxDcaCtrlTg0Ln3_p2.TxDcaFinePUTg0Ln3;
		this.TxDcaFinePUTg0Ln3 = this.TxDcaCtrlTg0Ln3_p2.TxDcaFinePUTg0Ln3;
		this.TxDcaCtrlTg0Ln3_p2_TxDcaFinePDTg0Ln3 = this.TxDcaCtrlTg0Ln3_p2.TxDcaFinePDTg0Ln3;
		this.TxDcaFinePDTg0Ln3 = this.TxDcaCtrlTg0Ln3_p2.TxDcaFinePDTg0Ln3;
      this.TxDcaCtrlTg1Ln3_p2 = ral_reg_DWC_DDRPHYA_HMDBYTE4_2_p2_TxDcaCtrlTg1Ln3_p2::type_id::create("TxDcaCtrlTg1Ln3_p2",,get_full_name());
      if(this.TxDcaCtrlTg1Ln3_p2.has_coverage(UVM_CVR_ALL))
      	this.TxDcaCtrlTg1Ln3_p2.cg_bits.option.name = {get_name(), ".", "TxDcaCtrlTg1Ln3_p2_bits"};
      this.TxDcaCtrlTg1Ln3_p2.configure(this, null, "");
      this.TxDcaCtrlTg1Ln3_p2.build();
      this.default_map.add_reg(this.TxDcaCtrlTg1Ln3_p2, `UVM_REG_ADDR_WIDTH'h631, "RW", 0);
		this.TxDcaCtrlTg1Ln3_p2_TxDcaCoarseTg1Ln3 = this.TxDcaCtrlTg1Ln3_p2.TxDcaCoarseTg1Ln3;
		this.TxDcaCoarseTg1Ln3 = this.TxDcaCtrlTg1Ln3_p2.TxDcaCoarseTg1Ln3;
		this.TxDcaCtrlTg1Ln3_p2_TxDcaFinePUTg1Ln3 = this.TxDcaCtrlTg1Ln3_p2.TxDcaFinePUTg1Ln3;
		this.TxDcaFinePUTg1Ln3 = this.TxDcaCtrlTg1Ln3_p2.TxDcaFinePUTg1Ln3;
		this.TxDcaCtrlTg1Ln3_p2_TxDcaFinePDTg1Ln3 = this.TxDcaCtrlTg1Ln3_p2.TxDcaFinePDTg1Ln3;
		this.TxDcaFinePDTg1Ln3 = this.TxDcaCtrlTg1Ln3_p2.TxDcaFinePDTg1Ln3;
   endfunction : build

	`uvm_object_utils(ral_block_DWC_DDRPHYA_HMDBYTE4_2_p2)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_DDRPHYA_HMDBYTE4_2_p2


endpackage
`endif
