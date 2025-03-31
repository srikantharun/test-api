`ifndef RAL_DWC_DDRCTL_MAP_REGB_FREQ0_CH0_PKG
`define RAL_DWC_DDRCTL_MAP_REGB_FREQ0_CH0_PKG

package ral_DWC_ddrctl_map_REGB_FREQ0_CH0_pkg;
import uvm_pkg::*;

class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG0 extends uvm_reg;
	rand uvm_reg_field t_ras_min;
	rand uvm_reg_field t_ras_max;
	rand uvm_reg_field t_faw;
	rand uvm_reg_field wr2pre;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   t_ras_min: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	   t_ras_max: coverpoint {m_data[15:8], m_is_read} iff(m_be) {
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
	   t_faw: coverpoint {m_data[23:16], m_is_read} iff(m_be) {
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
	   wr2pre: coverpoint {m_data[31:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.t_ras_min = uvm_reg_field::type_id::create("t_ras_min",,get_full_name());
      this.t_ras_min.configure(this, 8, 0, "RW", 1, 8'hf, 1, 0, 1);
      this.t_ras_max = uvm_reg_field::type_id::create("t_ras_max",,get_full_name());
      this.t_ras_max.configure(this, 8, 8, "RW", 1, 8'h1b, 1, 0, 1);
      this.t_faw = uvm_reg_field::type_id::create("t_faw",,get_full_name());
      this.t_faw.configure(this, 8, 16, "RW", 1, 8'h10, 1, 0, 1);
      this.wr2pre = uvm_reg_field::type_id::create("wr2pre",,get_full_name());
      this.wr2pre.configure(this, 8, 24, "RW", 1, 8'hf, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG0


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG1 extends uvm_reg;
	rand uvm_reg_field t_rc;
	rand uvm_reg_field rd2pre;
	rand uvm_reg_field t_xp;
	rand uvm_reg_field t_rcd_write;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   t_rc: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	   rd2pre: coverpoint {m_data[15:8], m_is_read} iff(m_be) {
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
	   t_xp: coverpoint {m_data[21:16], m_is_read} iff(m_be) {
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
	   t_rcd_write: coverpoint {m_data[31:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG1");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.t_rc = uvm_reg_field::type_id::create("t_rc",,get_full_name());
      this.t_rc.configure(this, 8, 0, "RW", 1, 8'h14, 1, 0, 1);
      this.rd2pre = uvm_reg_field::type_id::create("rd2pre",,get_full_name());
      this.rd2pre.configure(this, 8, 8, "RW", 1, 8'h4, 1, 0, 1);
      this.t_xp = uvm_reg_field::type_id::create("t_xp",,get_full_name());
      this.t_xp.configure(this, 6, 16, "RW", 1, 6'h8, 1, 0, 1);
      this.t_rcd_write = uvm_reg_field::type_id::create("t_rcd_write",,get_full_name());
      this.t_rcd_write.configure(this, 8, 24, "RW", 1, 8'h5, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG1


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG2 extends uvm_reg;
	rand uvm_reg_field wr2rd;
	rand uvm_reg_field rd2wr;
	rand uvm_reg_field read_latency;
	rand uvm_reg_field write_latency;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   wr2rd: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	   rd2wr: coverpoint {m_data[15:8], m_is_read} iff(m_be) {
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
	   read_latency: coverpoint {m_data[22:16], m_is_read} iff(m_be) {
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
	   write_latency: coverpoint {m_data[30:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG2");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.wr2rd = uvm_reg_field::type_id::create("wr2rd",,get_full_name());
      this.wr2rd.configure(this, 8, 0, "RW", 1, 8'hd, 1, 0, 1);
      this.rd2wr = uvm_reg_field::type_id::create("rd2wr",,get_full_name());
      this.rd2wr.configure(this, 8, 8, "RW", 1, 8'h6, 1, 0, 1);
      this.read_latency = uvm_reg_field::type_id::create("read_latency",,get_full_name());
      this.read_latency.configure(this, 7, 16, "RW", 1, 7'h5, 1, 0, 1);
      this.write_latency = uvm_reg_field::type_id::create("write_latency",,get_full_name());
      this.write_latency.configure(this, 7, 24, "RW", 1, 7'h3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG2


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG3 extends uvm_reg;
	rand uvm_reg_field wr2mr;
	rand uvm_reg_field rd2mr;
	rand uvm_reg_field t_mr;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   wr2mr: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	   rd2mr: coverpoint {m_data[15:8], m_is_read} iff(m_be) {
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
	   t_mr: coverpoint {m_data[22:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG3");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.wr2mr = uvm_reg_field::type_id::create("wr2mr",,get_full_name());
      this.wr2mr.configure(this, 8, 0, "RW", 1, 8'h4, 1, 0, 1);
      this.rd2mr = uvm_reg_field::type_id::create("rd2mr",,get_full_name());
      this.rd2mr.configure(this, 8, 8, "RW", 1, 8'h4, 1, 0, 1);
      this.t_mr = uvm_reg_field::type_id::create("t_mr",,get_full_name());
      this.t_mr.configure(this, 7, 16, "RW", 1, 7'h4, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG3


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG4 extends uvm_reg;
	rand uvm_reg_field t_rp;
	rand uvm_reg_field t_rrd;
	rand uvm_reg_field t_ccd;
	rand uvm_reg_field t_rcd;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   t_rp: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   t_rrd: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	   t_ccd: coverpoint {m_data[21:16], m_is_read} iff(m_be) {
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
	   t_rcd: coverpoint {m_data[31:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG4");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.t_rp = uvm_reg_field::type_id::create("t_rp",,get_full_name());
      this.t_rp.configure(this, 7, 0, "RW", 1, 7'h5, 1, 0, 1);
      this.t_rrd = uvm_reg_field::type_id::create("t_rrd",,get_full_name());
      this.t_rrd.configure(this, 6, 8, "RW", 1, 6'h4, 1, 0, 1);
      this.t_ccd = uvm_reg_field::type_id::create("t_ccd",,get_full_name());
      this.t_ccd.configure(this, 6, 16, "RW", 1, 6'h4, 1, 0, 1);
      this.t_rcd = uvm_reg_field::type_id::create("t_rcd",,get_full_name());
      this.t_rcd.configure(this, 8, 24, "RW", 1, 8'h5, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG4)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG4


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG5 extends uvm_reg;
	rand uvm_reg_field t_cke;
	rand uvm_reg_field t_ckesr;
	rand uvm_reg_field t_cksre;
	rand uvm_reg_field t_cksrx;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   t_cke: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
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
	   t_ckesr: coverpoint {m_data[14:8], m_is_read} iff(m_be) {
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
	   t_cksre: coverpoint {m_data[22:16], m_is_read} iff(m_be) {
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
	   t_cksrx: coverpoint {m_data[29:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG5");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.t_cke = uvm_reg_field::type_id::create("t_cke",,get_full_name());
      this.t_cke.configure(this, 6, 0, "RW", 1, 6'h3, 1, 0, 1);
      this.t_ckesr = uvm_reg_field::type_id::create("t_ckesr",,get_full_name());
      this.t_ckesr.configure(this, 7, 8, "RW", 1, 7'h4, 1, 0, 1);
      this.t_cksre = uvm_reg_field::type_id::create("t_cksre",,get_full_name());
      this.t_cksre.configure(this, 7, 16, "RW", 1, 7'h5, 1, 0, 1);
      this.t_cksrx = uvm_reg_field::type_id::create("t_cksrx",,get_full_name());
      this.t_cksrx.configure(this, 6, 24, "RW", 1, 6'h5, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG5)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG5


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG6 extends uvm_reg;
	rand uvm_reg_field t_ckcsx;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   t_ckcsx: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG6");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.t_ckcsx = uvm_reg_field::type_id::create("t_ckcsx",,get_full_name());
      this.t_ckcsx.configure(this, 6, 0, "RW", 1, 6'h5, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG6)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG6


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG7 extends uvm_reg;
	rand uvm_reg_field t_csh;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   t_csh: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG7");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.t_csh = uvm_reg_field::type_id::create("t_csh",,get_full_name());
      this.t_csh.configure(this, 4, 0, "RW", 1, 4'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG7)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG7


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG9 extends uvm_reg;
	rand uvm_reg_field wr2rd_s;
	rand uvm_reg_field t_rrd_s;
	rand uvm_reg_field t_ccd_s;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   wr2rd_s: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	   t_rrd_s: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	   t_ccd_s: coverpoint {m_data[20:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG9");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.wr2rd_s = uvm_reg_field::type_id::create("wr2rd_s",,get_full_name());
      this.wr2rd_s.configure(this, 8, 0, "RW", 1, 8'hd, 1, 0, 1);
      this.t_rrd_s = uvm_reg_field::type_id::create("t_rrd_s",,get_full_name());
      this.t_rrd_s.configure(this, 6, 8, "RW", 1, 6'h4, 1, 0, 1);
      this.t_ccd_s = uvm_reg_field::type_id::create("t_ccd_s",,get_full_name());
      this.t_ccd_s.configure(this, 5, 16, "RW", 1, 5'h4, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG9)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG9


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG12 extends uvm_reg;
	rand uvm_reg_field t_cmdcke;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   t_cmdcke: coverpoint {m_data[19:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG12");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.t_cmdcke = uvm_reg_field::type_id::create("t_cmdcke",,get_full_name());
      this.t_cmdcke.configure(this, 4, 16, "RW", 1, 4'h2, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG12)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG12


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG13 extends uvm_reg;
	rand uvm_reg_field t_ppd;
	rand uvm_reg_field t_ccd_mw;
	rand uvm_reg_field odtloff;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   t_ppd: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   t_ccd_mw: coverpoint {m_data[22:16], m_is_read} iff(m_be) {
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
	   odtloff: coverpoint {m_data[30:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG13");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.t_ppd = uvm_reg_field::type_id::create("t_ppd",,get_full_name());
      this.t_ppd.configure(this, 4, 0, "RW", 1, 4'h4, 1, 0, 1);
      this.t_ccd_mw = uvm_reg_field::type_id::create("t_ccd_mw",,get_full_name());
      this.t_ccd_mw.configure(this, 7, 16, "RW", 1, 7'h20, 1, 0, 1);
      this.odtloff = uvm_reg_field::type_id::create("odtloff",,get_full_name());
      this.odtloff.configure(this, 7, 24, "RW", 1, 7'h1c, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG13)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG13


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG14 extends uvm_reg;
	rand uvm_reg_field t_xsr;
	rand uvm_reg_field t_osco;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   t_xsr: coverpoint {m_data[11:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {13'b???????????00};
	      wildcard bins bit_0_wr_as_1 = {13'b???????????10};
	      wildcard bins bit_0_rd_as_0 = {13'b???????????01};
	      wildcard bins bit_0_rd_as_1 = {13'b???????????11};
	      wildcard bins bit_1_wr_as_0 = {13'b??????????0?0};
	      wildcard bins bit_1_wr_as_1 = {13'b??????????1?0};
	      wildcard bins bit_1_rd_as_0 = {13'b??????????0?1};
	      wildcard bins bit_1_rd_as_1 = {13'b??????????1?1};
	      wildcard bins bit_2_wr_as_0 = {13'b?????????0??0};
	      wildcard bins bit_2_wr_as_1 = {13'b?????????1??0};
	      wildcard bins bit_2_rd_as_0 = {13'b?????????0??1};
	      wildcard bins bit_2_rd_as_1 = {13'b?????????1??1};
	      wildcard bins bit_3_wr_as_0 = {13'b????????0???0};
	      wildcard bins bit_3_wr_as_1 = {13'b????????1???0};
	      wildcard bins bit_3_rd_as_0 = {13'b????????0???1};
	      wildcard bins bit_3_rd_as_1 = {13'b????????1???1};
	      wildcard bins bit_4_wr_as_0 = {13'b???????0????0};
	      wildcard bins bit_4_wr_as_1 = {13'b???????1????0};
	      wildcard bins bit_4_rd_as_0 = {13'b???????0????1};
	      wildcard bins bit_4_rd_as_1 = {13'b???????1????1};
	      wildcard bins bit_5_wr_as_0 = {13'b??????0?????0};
	      wildcard bins bit_5_wr_as_1 = {13'b??????1?????0};
	      wildcard bins bit_5_rd_as_0 = {13'b??????0?????1};
	      wildcard bins bit_5_rd_as_1 = {13'b??????1?????1};
	      wildcard bins bit_6_wr_as_0 = {13'b?????0??????0};
	      wildcard bins bit_6_wr_as_1 = {13'b?????1??????0};
	      wildcard bins bit_6_rd_as_0 = {13'b?????0??????1};
	      wildcard bins bit_6_rd_as_1 = {13'b?????1??????1};
	      wildcard bins bit_7_wr_as_0 = {13'b????0???????0};
	      wildcard bins bit_7_wr_as_1 = {13'b????1???????0};
	      wildcard bins bit_7_rd_as_0 = {13'b????0???????1};
	      wildcard bins bit_7_rd_as_1 = {13'b????1???????1};
	      wildcard bins bit_8_wr_as_0 = {13'b???0????????0};
	      wildcard bins bit_8_wr_as_1 = {13'b???1????????0};
	      wildcard bins bit_8_rd_as_0 = {13'b???0????????1};
	      wildcard bins bit_8_rd_as_1 = {13'b???1????????1};
	      wildcard bins bit_9_wr_as_0 = {13'b??0?????????0};
	      wildcard bins bit_9_wr_as_1 = {13'b??1?????????0};
	      wildcard bins bit_9_rd_as_0 = {13'b??0?????????1};
	      wildcard bins bit_9_rd_as_1 = {13'b??1?????????1};
	      wildcard bins bit_10_wr_as_0 = {13'b?0??????????0};
	      wildcard bins bit_10_wr_as_1 = {13'b?1??????????0};
	      wildcard bins bit_10_rd_as_0 = {13'b?0??????????1};
	      wildcard bins bit_10_rd_as_1 = {13'b?1??????????1};
	      wildcard bins bit_11_wr_as_0 = {13'b0???????????0};
	      wildcard bins bit_11_wr_as_1 = {13'b1???????????0};
	      wildcard bins bit_11_rd_as_0 = {13'b0???????????1};
	      wildcard bins bit_11_rd_as_1 = {13'b1???????????1};
	      option.weight = 48;
	   }
	   t_osco: coverpoint {m_data[24:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG14");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.t_xsr = uvm_reg_field::type_id::create("t_xsr",,get_full_name());
      this.t_xsr.configure(this, 12, 0, "RW", 1, 12'ha0, 1, 0, 1);
      this.t_osco = uvm_reg_field::type_id::create("t_osco",,get_full_name());
      this.t_osco.configure(this, 9, 16, "RW", 1, 9'h8, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG14)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG14


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG17 extends uvm_reg;
	rand uvm_reg_field t_vrcg_disable;
	rand uvm_reg_field t_vrcg_enable;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   t_vrcg_disable: coverpoint {m_data[9:0], m_is_read} iff(m_be) {
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
	   t_vrcg_enable: coverpoint {m_data[25:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG17");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.t_vrcg_disable = uvm_reg_field::type_id::create("t_vrcg_disable",,get_full_name());
      this.t_vrcg_disable.configure(this, 10, 0, "RW", 1, 10'h0, 1, 0, 1);
      this.t_vrcg_enable = uvm_reg_field::type_id::create("t_vrcg_enable",,get_full_name());
      this.t_vrcg_enable.configure(this, 10, 16, "RW", 1, 10'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG17)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG17


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG23 extends uvm_reg;
	rand uvm_reg_field t_pdn;
	rand uvm_reg_field t_xsr_dsm_x1024;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   t_pdn: coverpoint {m_data[11:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {13'b???????????00};
	      wildcard bins bit_0_wr_as_1 = {13'b???????????10};
	      wildcard bins bit_0_rd_as_0 = {13'b???????????01};
	      wildcard bins bit_0_rd_as_1 = {13'b???????????11};
	      wildcard bins bit_1_wr_as_0 = {13'b??????????0?0};
	      wildcard bins bit_1_wr_as_1 = {13'b??????????1?0};
	      wildcard bins bit_1_rd_as_0 = {13'b??????????0?1};
	      wildcard bins bit_1_rd_as_1 = {13'b??????????1?1};
	      wildcard bins bit_2_wr_as_0 = {13'b?????????0??0};
	      wildcard bins bit_2_wr_as_1 = {13'b?????????1??0};
	      wildcard bins bit_2_rd_as_0 = {13'b?????????0??1};
	      wildcard bins bit_2_rd_as_1 = {13'b?????????1??1};
	      wildcard bins bit_3_wr_as_0 = {13'b????????0???0};
	      wildcard bins bit_3_wr_as_1 = {13'b????????1???0};
	      wildcard bins bit_3_rd_as_0 = {13'b????????0???1};
	      wildcard bins bit_3_rd_as_1 = {13'b????????1???1};
	      wildcard bins bit_4_wr_as_0 = {13'b???????0????0};
	      wildcard bins bit_4_wr_as_1 = {13'b???????1????0};
	      wildcard bins bit_4_rd_as_0 = {13'b???????0????1};
	      wildcard bins bit_4_rd_as_1 = {13'b???????1????1};
	      wildcard bins bit_5_wr_as_0 = {13'b??????0?????0};
	      wildcard bins bit_5_wr_as_1 = {13'b??????1?????0};
	      wildcard bins bit_5_rd_as_0 = {13'b??????0?????1};
	      wildcard bins bit_5_rd_as_1 = {13'b??????1?????1};
	      wildcard bins bit_6_wr_as_0 = {13'b?????0??????0};
	      wildcard bins bit_6_wr_as_1 = {13'b?????1??????0};
	      wildcard bins bit_6_rd_as_0 = {13'b?????0??????1};
	      wildcard bins bit_6_rd_as_1 = {13'b?????1??????1};
	      wildcard bins bit_7_wr_as_0 = {13'b????0???????0};
	      wildcard bins bit_7_wr_as_1 = {13'b????1???????0};
	      wildcard bins bit_7_rd_as_0 = {13'b????0???????1};
	      wildcard bins bit_7_rd_as_1 = {13'b????1???????1};
	      wildcard bins bit_8_wr_as_0 = {13'b???0????????0};
	      wildcard bins bit_8_wr_as_1 = {13'b???1????????0};
	      wildcard bins bit_8_rd_as_0 = {13'b???0????????1};
	      wildcard bins bit_8_rd_as_1 = {13'b???1????????1};
	      wildcard bins bit_9_wr_as_0 = {13'b??0?????????0};
	      wildcard bins bit_9_wr_as_1 = {13'b??1?????????0};
	      wildcard bins bit_9_rd_as_0 = {13'b??0?????????1};
	      wildcard bins bit_9_rd_as_1 = {13'b??1?????????1};
	      wildcard bins bit_10_wr_as_0 = {13'b?0??????????0};
	      wildcard bins bit_10_wr_as_1 = {13'b?1??????????0};
	      wildcard bins bit_10_rd_as_0 = {13'b?0??????????1};
	      wildcard bins bit_10_rd_as_1 = {13'b?1??????????1};
	      wildcard bins bit_11_wr_as_0 = {13'b0???????????0};
	      wildcard bins bit_11_wr_as_1 = {13'b1???????????0};
	      wildcard bins bit_11_rd_as_0 = {13'b0???????????1};
	      wildcard bins bit_11_rd_as_1 = {13'b1???????????1};
	      option.weight = 48;
	   }
	   t_xsr_dsm_x1024: coverpoint {m_data[23:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG23");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.t_pdn = uvm_reg_field::type_id::create("t_pdn",,get_full_name());
      this.t_pdn.configure(this, 12, 0, "RW", 0, 12'h0, 1, 0, 1);
      this.t_xsr_dsm_x1024 = uvm_reg_field::type_id::create("t_xsr_dsm_x1024",,get_full_name());
      this.t_xsr_dsm_x1024.configure(this, 8, 16, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG23)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG23


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG24 extends uvm_reg;
	rand uvm_reg_field max_wr_sync;
	rand uvm_reg_field max_rd_sync;
	rand uvm_reg_field rd2wr_s;
	rand uvm_reg_field bank_org;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   max_wr_sync: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	   max_rd_sync: coverpoint {m_data[15:8], m_is_read} iff(m_be) {
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
	   rd2wr_s: coverpoint {m_data[23:16], m_is_read} iff(m_be) {
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
	   bank_org: coverpoint {m_data[25:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG24");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.max_wr_sync = uvm_reg_field::type_id::create("max_wr_sync",,get_full_name());
      this.max_wr_sync.configure(this, 8, 0, "RW", 1, 8'hf, 1, 0, 1);
      this.max_rd_sync = uvm_reg_field::type_id::create("max_rd_sync",,get_full_name());
      this.max_rd_sync.configure(this, 8, 8, "RW", 1, 8'hf, 1, 0, 1);
      this.rd2wr_s = uvm_reg_field::type_id::create("rd2wr_s",,get_full_name());
      this.rd2wr_s.configure(this, 8, 16, "RW", 1, 8'hf, 1, 0, 1);
      this.bank_org = uvm_reg_field::type_id::create("bank_org",,get_full_name());
      this.bank_org.configure(this, 2, 24, "RW", 1, 2'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG24)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG24


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG25 extends uvm_reg;
	rand uvm_reg_field rda2pre;
	rand uvm_reg_field wra2pre;
	rand uvm_reg_field lpddr4_diff_bank_rwa2pre;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   rda2pre: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	   wra2pre: coverpoint {m_data[15:8], m_is_read} iff(m_be) {
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
	   lpddr4_diff_bank_rwa2pre: coverpoint {m_data[18:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG25");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.rda2pre = uvm_reg_field::type_id::create("rda2pre",,get_full_name());
      this.rda2pre.configure(this, 8, 0, "RW", 1, 8'h0, 1, 0, 1);
      this.wra2pre = uvm_reg_field::type_id::create("wra2pre",,get_full_name());
      this.wra2pre.configure(this, 8, 8, "RW", 1, 8'h0, 1, 0, 1);
      this.lpddr4_diff_bank_rwa2pre = uvm_reg_field::type_id::create("lpddr4_diff_bank_rwa2pre",,get_full_name());
      this.lpddr4_diff_bank_rwa2pre.configure(this, 3, 16, "RW", 1, 3'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG25)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG25


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG30 extends uvm_reg;
	rand uvm_reg_field mrr2rd;
	rand uvm_reg_field mrr2wr;
	rand uvm_reg_field mrr2mrw;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   mrr2rd: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	   mrr2wr: coverpoint {m_data[15:8], m_is_read} iff(m_be) {
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
	   mrr2mrw: coverpoint {m_data[23:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG30");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.mrr2rd = uvm_reg_field::type_id::create("mrr2rd",,get_full_name());
      this.mrr2rd.configure(this, 8, 0, "RW", 1, 8'h0, 1, 0, 1);
      this.mrr2wr = uvm_reg_field::type_id::create("mrr2wr",,get_full_name());
      this.mrr2wr.configure(this, 8, 8, "RW", 1, 8'h0, 1, 0, 1);
      this.mrr2mrw = uvm_reg_field::type_id::create("mrr2mrw",,get_full_name());
      this.mrr2mrw.configure(this, 8, 16, "RW", 1, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG30)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG30


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG32 extends uvm_reg;
	rand uvm_reg_field ws_fs2wck_sus;
	rand uvm_reg_field t_wcksus;
	rand uvm_reg_field ws_off2ws_fs;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ws_fs2wck_sus: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   t_wcksus: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	   ws_off2ws_fs: coverpoint {m_data[19:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG32");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ws_fs2wck_sus = uvm_reg_field::type_id::create("ws_fs2wck_sus",,get_full_name());
      this.ws_fs2wck_sus.configure(this, 4, 0, "RW", 1, 4'h8, 1, 0, 1);
      this.t_wcksus = uvm_reg_field::type_id::create("t_wcksus",,get_full_name());
      this.t_wcksus.configure(this, 4, 8, "RW", 1, 4'h4, 1, 0, 1);
      this.ws_off2ws_fs = uvm_reg_field::type_id::create("ws_off2ws_fs",,get_full_name());
      this.ws_off2ws_fs.configure(this, 4, 16, "RW", 1, 4'h3, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG32)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG32


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR0 extends uvm_reg;
	rand uvm_reg_field emr;
	rand uvm_reg_field mr;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   emr: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	   mr: coverpoint {m_data[31:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.emr = uvm_reg_field::type_id::create("emr",,get_full_name());
      this.emr.configure(this, 16, 0, "RW", 1, 16'h510, 1, 0, 1);
      this.mr = uvm_reg_field::type_id::create("mr",,get_full_name());
      this.mr.configure(this, 16, 16, "RW", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR0


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR1 extends uvm_reg;
	rand uvm_reg_field emr3;
	rand uvm_reg_field emr2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   emr3: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	   emr2: coverpoint {m_data[31:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR1");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.emr3 = uvm_reg_field::type_id::create("emr3",,get_full_name());
      this.emr3.configure(this, 16, 0, "RW", 1, 16'h0, 1, 0, 1);
      this.emr2 = uvm_reg_field::type_id::create("emr2",,get_full_name());
      this.emr2.configure(this, 16, 16, "RW", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR1


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR2 extends uvm_reg;
	rand uvm_reg_field mr5;
	rand uvm_reg_field mr4;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   mr5: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	   mr4: coverpoint {m_data[31:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR2");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.mr5 = uvm_reg_field::type_id::create("mr5",,get_full_name());
      this.mr5.configure(this, 16, 0, "RW", 1, 16'h0, 1, 0, 1);
      this.mr4 = uvm_reg_field::type_id::create("mr4",,get_full_name());
      this.mr4.configure(this, 16, 16, "RW", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR2


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR3 extends uvm_reg;
	rand uvm_reg_field mr6;
	rand uvm_reg_field mr22;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   mr6: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	   mr22: coverpoint {m_data[31:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR3");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.mr6 = uvm_reg_field::type_id::create("mr6",,get_full_name());
      this.mr6.configure(this, 16, 0, "RW", 1, 16'h0, 1, 0, 1);
      this.mr22 = uvm_reg_field::type_id::create("mr22",,get_full_name());
      this.mr22.configure(this, 16, 16, "RW", 1, 16'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR3


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG0 extends uvm_reg;
	rand uvm_reg_field dfi_tphy_wrlat;
	rand uvm_reg_field dfi_tphy_wrdata;
	rand uvm_reg_field dfi_t_rddata_en;
	rand uvm_reg_field dfi_t_ctrl_delay;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dfi_tphy_wrlat: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   dfi_tphy_wrdata: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	   dfi_t_rddata_en: coverpoint {m_data[22:16], m_is_read} iff(m_be) {
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
	   dfi_t_ctrl_delay: coverpoint {m_data[28:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dfi_tphy_wrlat = uvm_reg_field::type_id::create("dfi_tphy_wrlat",,get_full_name());
      this.dfi_tphy_wrlat.configure(this, 7, 0, "RW", 1, 7'h2, 1, 0, 1);
      this.dfi_tphy_wrdata = uvm_reg_field::type_id::create("dfi_tphy_wrdata",,get_full_name());
      this.dfi_tphy_wrdata.configure(this, 6, 8, "RW", 1, 6'h0, 1, 0, 1);
      this.dfi_t_rddata_en = uvm_reg_field::type_id::create("dfi_t_rddata_en",,get_full_name());
      this.dfi_t_rddata_en.configure(this, 7, 16, "RW", 1, 7'h2, 1, 0, 1);
      this.dfi_t_ctrl_delay = uvm_reg_field::type_id::create("dfi_t_ctrl_delay",,get_full_name());
      this.dfi_t_ctrl_delay.configure(this, 5, 24, "RW", 1, 5'h7, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG0


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG1 extends uvm_reg;
	rand uvm_reg_field dfi_t_dram_clk_enable;
	rand uvm_reg_field dfi_t_dram_clk_disable;
	rand uvm_reg_field dfi_t_wrdata_delay;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dfi_t_dram_clk_enable: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	   dfi_t_dram_clk_disable: coverpoint {m_data[12:8], m_is_read} iff(m_be) {
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
	   dfi_t_wrdata_delay: coverpoint {m_data[20:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG1");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dfi_t_dram_clk_enable = uvm_reg_field::type_id::create("dfi_t_dram_clk_enable",,get_full_name());
      this.dfi_t_dram_clk_enable.configure(this, 5, 0, "RW", 1, 5'h4, 1, 0, 1);
      this.dfi_t_dram_clk_disable = uvm_reg_field::type_id::create("dfi_t_dram_clk_disable",,get_full_name());
      this.dfi_t_dram_clk_disable.configure(this, 5, 8, "RW", 1, 5'h4, 1, 0, 1);
      this.dfi_t_wrdata_delay = uvm_reg_field::type_id::create("dfi_t_wrdata_delay",,get_full_name());
      this.dfi_t_wrdata_delay.configure(this, 5, 16, "RW", 1, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG1


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG2 extends uvm_reg;
	rand uvm_reg_field dfi_tphy_wrcslat;
	rand uvm_reg_field dfi_tphy_rdcslat;
	rand uvm_reg_field dfi_twck_delay;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dfi_tphy_wrcslat: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   dfi_tphy_rdcslat: coverpoint {m_data[14:8], m_is_read} iff(m_be) {
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
	   dfi_twck_delay: coverpoint {m_data[21:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG2");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dfi_tphy_wrcslat = uvm_reg_field::type_id::create("dfi_tphy_wrcslat",,get_full_name());
      this.dfi_tphy_wrcslat.configure(this, 7, 0, "RW", 1, 7'h2, 1, 0, 1);
      this.dfi_tphy_rdcslat = uvm_reg_field::type_id::create("dfi_tphy_rdcslat",,get_full_name());
      this.dfi_tphy_rdcslat.configure(this, 7, 8, "RW", 1, 7'h2, 1, 0, 1);
      this.dfi_twck_delay = uvm_reg_field::type_id::create("dfi_twck_delay",,get_full_name());
      this.dfi_twck_delay.configure(this, 6, 16, "RW", 1, 6'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG2


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG4 extends uvm_reg;
	rand uvm_reg_field dfi_twck_dis;
	rand uvm_reg_field dfi_twck_en_fs;
	rand uvm_reg_field dfi_twck_en_wr;
	rand uvm_reg_field dfi_twck_en_rd;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dfi_twck_dis: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	   dfi_twck_en_fs: coverpoint {m_data[15:8], m_is_read} iff(m_be) {
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
	   dfi_twck_en_wr: coverpoint {m_data[23:16], m_is_read} iff(m_be) {
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
	   dfi_twck_en_rd: coverpoint {m_data[31:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG4");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dfi_twck_dis = uvm_reg_field::type_id::create("dfi_twck_dis",,get_full_name());
      this.dfi_twck_dis.configure(this, 8, 0, "RW", 1, 8'h0, 1, 0, 1);
      this.dfi_twck_en_fs = uvm_reg_field::type_id::create("dfi_twck_en_fs",,get_full_name());
      this.dfi_twck_en_fs.configure(this, 8, 8, "RW", 0, 8'h0, 1, 0, 1);
      this.dfi_twck_en_wr = uvm_reg_field::type_id::create("dfi_twck_en_wr",,get_full_name());
      this.dfi_twck_en_wr.configure(this, 8, 16, "RW", 1, 8'h0, 1, 0, 1);
      this.dfi_twck_en_rd = uvm_reg_field::type_id::create("dfi_twck_en_rd",,get_full_name());
      this.dfi_twck_en_rd.configure(this, 8, 24, "RW", 1, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG4)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG4


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG5 extends uvm_reg;
	rand uvm_reg_field dfi_twck_toggle_post;
	rand uvm_reg_field dfi_twck_toggle_cs;
	rand uvm_reg_field dfi_twck_toggle;
	rand uvm_reg_field dfi_twck_fast_toggle;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dfi_twck_toggle_post: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	   dfi_twck_toggle_cs: coverpoint {m_data[15:8], m_is_read} iff(m_be) {
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
	   dfi_twck_toggle: coverpoint {m_data[23:16], m_is_read} iff(m_be) {
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
	   dfi_twck_fast_toggle: coverpoint {m_data[31:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG5");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dfi_twck_toggle_post = uvm_reg_field::type_id::create("dfi_twck_toggle_post",,get_full_name());
      this.dfi_twck_toggle_post.configure(this, 8, 0, "RW", 1, 8'h0, 1, 0, 1);
      this.dfi_twck_toggle_cs = uvm_reg_field::type_id::create("dfi_twck_toggle_cs",,get_full_name());
      this.dfi_twck_toggle_cs.configure(this, 8, 8, "RW", 1, 8'h0, 1, 0, 1);
      this.dfi_twck_toggle = uvm_reg_field::type_id::create("dfi_twck_toggle",,get_full_name());
      this.dfi_twck_toggle.configure(this, 8, 16, "RW", 1, 8'h0, 1, 0, 1);
      this.dfi_twck_fast_toggle = uvm_reg_field::type_id::create("dfi_twck_fast_toggle",,get_full_name());
      this.dfi_twck_fast_toggle.configure(this, 8, 24, "RW", 1, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG5)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG5


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG6 extends uvm_reg;
	rand uvm_reg_field dfi_twck_toggle_post_rd;
	rand uvm_reg_field dfi_twck_toggle_post_rd_en;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dfi_twck_toggle_post_rd: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	   dfi_twck_toggle_post_rd_en: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG6");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dfi_twck_toggle_post_rd = uvm_reg_field::type_id::create("dfi_twck_toggle_post_rd",,get_full_name());
      this.dfi_twck_toggle_post_rd.configure(this, 8, 0, "RW", 1, 8'h0, 1, 0, 1);
      this.dfi_twck_toggle_post_rd_en = uvm_reg_field::type_id::create("dfi_twck_toggle_post_rd_en",,get_full_name());
      this.dfi_twck_toggle_post_rd_en.configure(this, 1, 8, "RW", 1, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG6)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG6


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFILPTMG0 extends uvm_reg;
	rand uvm_reg_field dfi_lp_wakeup_pd;
	rand uvm_reg_field dfi_lp_wakeup_sr;
	rand uvm_reg_field dfi_lp_wakeup_dsm;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dfi_lp_wakeup_pd: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	   dfi_lp_wakeup_sr: coverpoint {m_data[12:8], m_is_read} iff(m_be) {
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
	   dfi_lp_wakeup_dsm: coverpoint {m_data[20:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DFILPTMG0");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dfi_lp_wakeup_pd = uvm_reg_field::type_id::create("dfi_lp_wakeup_pd",,get_full_name());
      this.dfi_lp_wakeup_pd.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
      this.dfi_lp_wakeup_sr = uvm_reg_field::type_id::create("dfi_lp_wakeup_sr",,get_full_name());
      this.dfi_lp_wakeup_sr.configure(this, 5, 8, "RW", 0, 5'h0, 1, 0, 1);
      this.dfi_lp_wakeup_dsm = uvm_reg_field::type_id::create("dfi_lp_wakeup_dsm",,get_full_name());
      this.dfi_lp_wakeup_dsm.configure(this, 5, 16, "RW", 0, 5'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFILPTMG0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFILPTMG0


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFILPTMG1 extends uvm_reg;
	rand uvm_reg_field dfi_lp_wakeup_data;
	rand uvm_reg_field dfi_tlp_resp;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dfi_lp_wakeup_data: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	   dfi_tlp_resp: coverpoint {m_data[12:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DFILPTMG1");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dfi_lp_wakeup_data = uvm_reg_field::type_id::create("dfi_lp_wakeup_data",,get_full_name());
      this.dfi_lp_wakeup_data.configure(this, 5, 0, "RW", 0, 5'h0, 1, 0, 1);
      this.dfi_tlp_resp = uvm_reg_field::type_id::create("dfi_tlp_resp",,get_full_name());
      this.dfi_tlp_resp.configure(this, 5, 8, "RW", 0, 5'h7, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFILPTMG1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFILPTMG1


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG0 extends uvm_reg;
	rand uvm_reg_field dfi_t_ctrlup_min;
	rand uvm_reg_field dfi_t_ctrlup_max;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dfi_t_ctrlup_min: coverpoint {m_data[9:0], m_is_read} iff(m_be) {
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
	   dfi_t_ctrlup_max: coverpoint {m_data[25:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dfi_t_ctrlup_min = uvm_reg_field::type_id::create("dfi_t_ctrlup_min",,get_full_name());
      this.dfi_t_ctrlup_min.configure(this, 10, 0, "RW", 0, 10'h3, 1, 0, 1);
      this.dfi_t_ctrlup_max = uvm_reg_field::type_id::create("dfi_t_ctrlup_max",,get_full_name());
      this.dfi_t_ctrlup_max.configure(this, 10, 16, "RW", 0, 10'h40, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG0


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG1 extends uvm_reg;
	rand uvm_reg_field dfi_t_ctrlupd_interval_max_x1024;
	rand uvm_reg_field dfi_t_ctrlupd_interval_min_x1024;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dfi_t_ctrlupd_interval_max_x1024: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	   dfi_t_ctrlupd_interval_min_x1024: coverpoint {m_data[23:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG1");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dfi_t_ctrlupd_interval_max_x1024 = uvm_reg_field::type_id::create("dfi_t_ctrlupd_interval_max_x1024",,get_full_name());
      this.dfi_t_ctrlupd_interval_max_x1024.configure(this, 8, 0, "RW", 0, 8'h1, 1, 0, 1);
      this.dfi_t_ctrlupd_interval_min_x1024 = uvm_reg_field::type_id::create("dfi_t_ctrlupd_interval_min_x1024",,get_full_name());
      this.dfi_t_ctrlupd_interval_min_x1024.configure(this, 8, 16, "RW", 0, 8'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG1


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG2 extends uvm_reg;
	rand uvm_reg_field dfi_t_ctrlupd_interval_type1;
	rand uvm_reg_field ctrlupd_after_dqsosc;
	rand uvm_reg_field ppt2_override;
	rand uvm_reg_field ppt2_en;
	rand uvm_reg_field dfi_t_ctrlupd_interval_type1_unit;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dfi_t_ctrlupd_interval_type1: coverpoint {m_data[11:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {13'b???????????00};
	      wildcard bins bit_0_wr_as_1 = {13'b???????????10};
	      wildcard bins bit_0_rd_as_0 = {13'b???????????01};
	      wildcard bins bit_0_rd_as_1 = {13'b???????????11};
	      wildcard bins bit_1_wr_as_0 = {13'b??????????0?0};
	      wildcard bins bit_1_wr_as_1 = {13'b??????????1?0};
	      wildcard bins bit_1_rd_as_0 = {13'b??????????0?1};
	      wildcard bins bit_1_rd_as_1 = {13'b??????????1?1};
	      wildcard bins bit_2_wr_as_0 = {13'b?????????0??0};
	      wildcard bins bit_2_wr_as_1 = {13'b?????????1??0};
	      wildcard bins bit_2_rd_as_0 = {13'b?????????0??1};
	      wildcard bins bit_2_rd_as_1 = {13'b?????????1??1};
	      wildcard bins bit_3_wr_as_0 = {13'b????????0???0};
	      wildcard bins bit_3_wr_as_1 = {13'b????????1???0};
	      wildcard bins bit_3_rd_as_0 = {13'b????????0???1};
	      wildcard bins bit_3_rd_as_1 = {13'b????????1???1};
	      wildcard bins bit_4_wr_as_0 = {13'b???????0????0};
	      wildcard bins bit_4_wr_as_1 = {13'b???????1????0};
	      wildcard bins bit_4_rd_as_0 = {13'b???????0????1};
	      wildcard bins bit_4_rd_as_1 = {13'b???????1????1};
	      wildcard bins bit_5_wr_as_0 = {13'b??????0?????0};
	      wildcard bins bit_5_wr_as_1 = {13'b??????1?????0};
	      wildcard bins bit_5_rd_as_0 = {13'b??????0?????1};
	      wildcard bins bit_5_rd_as_1 = {13'b??????1?????1};
	      wildcard bins bit_6_wr_as_0 = {13'b?????0??????0};
	      wildcard bins bit_6_wr_as_1 = {13'b?????1??????0};
	      wildcard bins bit_6_rd_as_0 = {13'b?????0??????1};
	      wildcard bins bit_6_rd_as_1 = {13'b?????1??????1};
	      wildcard bins bit_7_wr_as_0 = {13'b????0???????0};
	      wildcard bins bit_7_wr_as_1 = {13'b????1???????0};
	      wildcard bins bit_7_rd_as_0 = {13'b????0???????1};
	      wildcard bins bit_7_rd_as_1 = {13'b????1???????1};
	      wildcard bins bit_8_wr_as_0 = {13'b???0????????0};
	      wildcard bins bit_8_wr_as_1 = {13'b???1????????0};
	      wildcard bins bit_8_rd_as_0 = {13'b???0????????1};
	      wildcard bins bit_8_rd_as_1 = {13'b???1????????1};
	      wildcard bins bit_9_wr_as_0 = {13'b??0?????????0};
	      wildcard bins bit_9_wr_as_1 = {13'b??1?????????0};
	      wildcard bins bit_9_rd_as_0 = {13'b??0?????????1};
	      wildcard bins bit_9_rd_as_1 = {13'b??1?????????1};
	      wildcard bins bit_10_wr_as_0 = {13'b?0??????????0};
	      wildcard bins bit_10_wr_as_1 = {13'b?1??????????0};
	      wildcard bins bit_10_rd_as_0 = {13'b?0??????????1};
	      wildcard bins bit_10_rd_as_1 = {13'b?1??????????1};
	      wildcard bins bit_11_wr_as_0 = {13'b0???????????0};
	      wildcard bins bit_11_wr_as_1 = {13'b1???????????0};
	      wildcard bins bit_11_rd_as_0 = {13'b0???????????1};
	      wildcard bins bit_11_rd_as_1 = {13'b1???????????1};
	      option.weight = 48;
	   }
	   ctrlupd_after_dqsosc: coverpoint {m_data[27:27], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ppt2_override: coverpoint {m_data[28:28], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ppt2_en: coverpoint {m_data[29:29], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dfi_t_ctrlupd_interval_type1_unit: coverpoint {m_data[31:30], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG2");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dfi_t_ctrlupd_interval_type1 = uvm_reg_field::type_id::create("dfi_t_ctrlupd_interval_type1",,get_full_name());
      this.dfi_t_ctrlupd_interval_type1.configure(this, 12, 0, "RW", 0, 12'h12c, 1, 0, 1);
      this.ctrlupd_after_dqsosc = uvm_reg_field::type_id::create("ctrlupd_after_dqsosc",,get_full_name());
      this.ctrlupd_after_dqsosc.configure(this, 1, 27, "RW", 0, 1'h0, 1, 0, 0);
      this.ppt2_override = uvm_reg_field::type_id::create("ppt2_override",,get_full_name());
      this.ppt2_override.configure(this, 1, 28, "RW", 0, 1'h0, 1, 0, 0);
      this.ppt2_en = uvm_reg_field::type_id::create("ppt2_en",,get_full_name());
      this.ppt2_en.configure(this, 1, 29, "RW", 0, 1'h0, 1, 0, 0);
      this.dfi_t_ctrlupd_interval_type1_unit = uvm_reg_field::type_id::create("dfi_t_ctrlupd_interval_type1_unit",,get_full_name());
      this.dfi_t_ctrlupd_interval_type1_unit.configure(this, 2, 30, "RW", 0, 2'h3, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG2


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG3 extends uvm_reg;
	rand uvm_reg_field dfi_t_ctrlupd_burst_interval_x8;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dfi_t_ctrlupd_burst_interval_x8: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG3");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dfi_t_ctrlupd_burst_interval_x8 = uvm_reg_field::type_id::create("dfi_t_ctrlupd_burst_interval_x8",,get_full_name());
      this.dfi_t_ctrlupd_burst_interval_x8.configure(this, 9, 0, "RW", 0, 9'h1, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG3


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG0 extends uvm_reg;
	rand uvm_reg_field t_refi_x1_x32;
	rand uvm_reg_field refresh_to_x1_x32;
	rand uvm_reg_field refresh_margin;
	rand uvm_reg_field refresh_to_x1_sel;
	rand uvm_reg_field t_refi_x1_sel;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   t_refi_x1_x32: coverpoint {m_data[13:0], m_is_read} iff(m_be) {
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
	   refresh_to_x1_x32: coverpoint {m_data[21:16], m_is_read} iff(m_be) {
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
	   refresh_margin: coverpoint {m_data[27:24], m_is_read} iff(m_be) {
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
	   refresh_to_x1_sel: coverpoint {m_data[30:30], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   t_refi_x1_sel: coverpoint {m_data[31:31], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.t_refi_x1_x32 = uvm_reg_field::type_id::create("t_refi_x1_x32",,get_full_name());
      this.t_refi_x1_x32.configure(this, 14, 0, "RW", 0, 14'h62, 1, 0, 1);
      this.refresh_to_x1_x32 = uvm_reg_field::type_id::create("refresh_to_x1_x32",,get_full_name());
      this.refresh_to_x1_x32.configure(this, 6, 16, "RW", 0, 6'h10, 1, 0, 1);
      this.refresh_margin = uvm_reg_field::type_id::create("refresh_margin",,get_full_name());
      this.refresh_margin.configure(this, 4, 24, "RW", 0, 4'h2, 1, 0, 0);
      this.refresh_to_x1_sel = uvm_reg_field::type_id::create("refresh_to_x1_sel",,get_full_name());
      this.refresh_to_x1_sel.configure(this, 1, 30, "RW", 0, 1'h0, 1, 0, 0);
      this.t_refi_x1_sel = uvm_reg_field::type_id::create("t_refi_x1_sel",,get_full_name());
      this.t_refi_x1_sel.configure(this, 1, 31, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG0


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG1 extends uvm_reg;
	rand uvm_reg_field t_rfc_min;
	rand uvm_reg_field t_rfc_min_ab;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   t_rfc_min: coverpoint {m_data[11:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {13'b???????????00};
	      wildcard bins bit_0_wr_as_1 = {13'b???????????10};
	      wildcard bins bit_0_rd_as_0 = {13'b???????????01};
	      wildcard bins bit_0_rd_as_1 = {13'b???????????11};
	      wildcard bins bit_1_wr_as_0 = {13'b??????????0?0};
	      wildcard bins bit_1_wr_as_1 = {13'b??????????1?0};
	      wildcard bins bit_1_rd_as_0 = {13'b??????????0?1};
	      wildcard bins bit_1_rd_as_1 = {13'b??????????1?1};
	      wildcard bins bit_2_wr_as_0 = {13'b?????????0??0};
	      wildcard bins bit_2_wr_as_1 = {13'b?????????1??0};
	      wildcard bins bit_2_rd_as_0 = {13'b?????????0??1};
	      wildcard bins bit_2_rd_as_1 = {13'b?????????1??1};
	      wildcard bins bit_3_wr_as_0 = {13'b????????0???0};
	      wildcard bins bit_3_wr_as_1 = {13'b????????1???0};
	      wildcard bins bit_3_rd_as_0 = {13'b????????0???1};
	      wildcard bins bit_3_rd_as_1 = {13'b????????1???1};
	      wildcard bins bit_4_wr_as_0 = {13'b???????0????0};
	      wildcard bins bit_4_wr_as_1 = {13'b???????1????0};
	      wildcard bins bit_4_rd_as_0 = {13'b???????0????1};
	      wildcard bins bit_4_rd_as_1 = {13'b???????1????1};
	      wildcard bins bit_5_wr_as_0 = {13'b??????0?????0};
	      wildcard bins bit_5_wr_as_1 = {13'b??????1?????0};
	      wildcard bins bit_5_rd_as_0 = {13'b??????0?????1};
	      wildcard bins bit_5_rd_as_1 = {13'b??????1?????1};
	      wildcard bins bit_6_wr_as_0 = {13'b?????0??????0};
	      wildcard bins bit_6_wr_as_1 = {13'b?????1??????0};
	      wildcard bins bit_6_rd_as_0 = {13'b?????0??????1};
	      wildcard bins bit_6_rd_as_1 = {13'b?????1??????1};
	      wildcard bins bit_7_wr_as_0 = {13'b????0???????0};
	      wildcard bins bit_7_wr_as_1 = {13'b????1???????0};
	      wildcard bins bit_7_rd_as_0 = {13'b????0???????1};
	      wildcard bins bit_7_rd_as_1 = {13'b????1???????1};
	      wildcard bins bit_8_wr_as_0 = {13'b???0????????0};
	      wildcard bins bit_8_wr_as_1 = {13'b???1????????0};
	      wildcard bins bit_8_rd_as_0 = {13'b???0????????1};
	      wildcard bins bit_8_rd_as_1 = {13'b???1????????1};
	      wildcard bins bit_9_wr_as_0 = {13'b??0?????????0};
	      wildcard bins bit_9_wr_as_1 = {13'b??1?????????0};
	      wildcard bins bit_9_rd_as_0 = {13'b??0?????????1};
	      wildcard bins bit_9_rd_as_1 = {13'b??1?????????1};
	      wildcard bins bit_10_wr_as_0 = {13'b?0??????????0};
	      wildcard bins bit_10_wr_as_1 = {13'b?1??????????0};
	      wildcard bins bit_10_rd_as_0 = {13'b?0??????????1};
	      wildcard bins bit_10_rd_as_1 = {13'b?1??????????1};
	      wildcard bins bit_11_wr_as_0 = {13'b0???????????0};
	      wildcard bins bit_11_wr_as_1 = {13'b1???????????0};
	      wildcard bins bit_11_rd_as_0 = {13'b0???????????1};
	      wildcard bins bit_11_rd_as_1 = {13'b1???????????1};
	      option.weight = 48;
	   }
	   t_rfc_min_ab: coverpoint {m_data[27:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {13'b???????????00};
	      wildcard bins bit_0_wr_as_1 = {13'b???????????10};
	      wildcard bins bit_0_rd_as_0 = {13'b???????????01};
	      wildcard bins bit_0_rd_as_1 = {13'b???????????11};
	      wildcard bins bit_1_wr_as_0 = {13'b??????????0?0};
	      wildcard bins bit_1_wr_as_1 = {13'b??????????1?0};
	      wildcard bins bit_1_rd_as_0 = {13'b??????????0?1};
	      wildcard bins bit_1_rd_as_1 = {13'b??????????1?1};
	      wildcard bins bit_2_wr_as_0 = {13'b?????????0??0};
	      wildcard bins bit_2_wr_as_1 = {13'b?????????1??0};
	      wildcard bins bit_2_rd_as_0 = {13'b?????????0??1};
	      wildcard bins bit_2_rd_as_1 = {13'b?????????1??1};
	      wildcard bins bit_3_wr_as_0 = {13'b????????0???0};
	      wildcard bins bit_3_wr_as_1 = {13'b????????1???0};
	      wildcard bins bit_3_rd_as_0 = {13'b????????0???1};
	      wildcard bins bit_3_rd_as_1 = {13'b????????1???1};
	      wildcard bins bit_4_wr_as_0 = {13'b???????0????0};
	      wildcard bins bit_4_wr_as_1 = {13'b???????1????0};
	      wildcard bins bit_4_rd_as_0 = {13'b???????0????1};
	      wildcard bins bit_4_rd_as_1 = {13'b???????1????1};
	      wildcard bins bit_5_wr_as_0 = {13'b??????0?????0};
	      wildcard bins bit_5_wr_as_1 = {13'b??????1?????0};
	      wildcard bins bit_5_rd_as_0 = {13'b??????0?????1};
	      wildcard bins bit_5_rd_as_1 = {13'b??????1?????1};
	      wildcard bins bit_6_wr_as_0 = {13'b?????0??????0};
	      wildcard bins bit_6_wr_as_1 = {13'b?????1??????0};
	      wildcard bins bit_6_rd_as_0 = {13'b?????0??????1};
	      wildcard bins bit_6_rd_as_1 = {13'b?????1??????1};
	      wildcard bins bit_7_wr_as_0 = {13'b????0???????0};
	      wildcard bins bit_7_wr_as_1 = {13'b????1???????0};
	      wildcard bins bit_7_rd_as_0 = {13'b????0???????1};
	      wildcard bins bit_7_rd_as_1 = {13'b????1???????1};
	      wildcard bins bit_8_wr_as_0 = {13'b???0????????0};
	      wildcard bins bit_8_wr_as_1 = {13'b???1????????0};
	      wildcard bins bit_8_rd_as_0 = {13'b???0????????1};
	      wildcard bins bit_8_rd_as_1 = {13'b???1????????1};
	      wildcard bins bit_9_wr_as_0 = {13'b??0?????????0};
	      wildcard bins bit_9_wr_as_1 = {13'b??1?????????0};
	      wildcard bins bit_9_rd_as_0 = {13'b??0?????????1};
	      wildcard bins bit_9_rd_as_1 = {13'b??1?????????1};
	      wildcard bins bit_10_wr_as_0 = {13'b?0??????????0};
	      wildcard bins bit_10_wr_as_1 = {13'b?1??????????0};
	      wildcard bins bit_10_rd_as_0 = {13'b?0??????????1};
	      wildcard bins bit_10_rd_as_1 = {13'b?1??????????1};
	      wildcard bins bit_11_wr_as_0 = {13'b0???????????0};
	      wildcard bins bit_11_wr_as_1 = {13'b1???????????0};
	      wildcard bins bit_11_rd_as_0 = {13'b0???????????1};
	      wildcard bins bit_11_rd_as_1 = {13'b1???????????1};
	      option.weight = 48;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG1");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.t_rfc_min = uvm_reg_field::type_id::create("t_rfc_min",,get_full_name());
      this.t_rfc_min.configure(this, 12, 0, "RW", 0, 12'h8c, 1, 0, 1);
      this.t_rfc_min_ab = uvm_reg_field::type_id::create("t_rfc_min_ab",,get_full_name());
      this.t_rfc_min_ab.configure(this, 12, 16, "RW", 0, 12'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG1


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG2 extends uvm_reg;
	rand uvm_reg_field t_pbr2pbr;
	rand uvm_reg_field t_pbr2act;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   t_pbr2pbr: coverpoint {m_data[23:16], m_is_read} iff(m_be) {
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
	   t_pbr2act: coverpoint {m_data[31:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG2");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.t_pbr2pbr = uvm_reg_field::type_id::create("t_pbr2pbr",,get_full_name());
      this.t_pbr2pbr.configure(this, 8, 16, "RW", 0, 8'h8c, 1, 0, 1);
      this.t_pbr2act = uvm_reg_field::type_id::create("t_pbr2act",,get_full_name());
      this.t_pbr2act.configure(this, 8, 24, "RW", 0, 8'h8c, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG2


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG3 extends uvm_reg;
	rand uvm_reg_field refresh_to_ab_x32;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   refresh_to_ab_x32: coverpoint {m_data[29:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG3");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.refresh_to_ab_x32 = uvm_reg_field::type_id::create("refresh_to_ab_x32",,get_full_name());
      this.refresh_to_ab_x32.configure(this, 6, 24, "RW", 0, 6'h10, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG3)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG3


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG4 extends uvm_reg;
	rand uvm_reg_field refresh_timer0_start_value_x32;
	rand uvm_reg_field refresh_timer1_start_value_x32;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   refresh_timer0_start_value_x32: coverpoint {m_data[11:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {13'b???????????00};
	      wildcard bins bit_0_wr_as_1 = {13'b???????????10};
	      wildcard bins bit_0_rd_as_0 = {13'b???????????01};
	      wildcard bins bit_0_rd_as_1 = {13'b???????????11};
	      wildcard bins bit_1_wr_as_0 = {13'b??????????0?0};
	      wildcard bins bit_1_wr_as_1 = {13'b??????????1?0};
	      wildcard bins bit_1_rd_as_0 = {13'b??????????0?1};
	      wildcard bins bit_1_rd_as_1 = {13'b??????????1?1};
	      wildcard bins bit_2_wr_as_0 = {13'b?????????0??0};
	      wildcard bins bit_2_wr_as_1 = {13'b?????????1??0};
	      wildcard bins bit_2_rd_as_0 = {13'b?????????0??1};
	      wildcard bins bit_2_rd_as_1 = {13'b?????????1??1};
	      wildcard bins bit_3_wr_as_0 = {13'b????????0???0};
	      wildcard bins bit_3_wr_as_1 = {13'b????????1???0};
	      wildcard bins bit_3_rd_as_0 = {13'b????????0???1};
	      wildcard bins bit_3_rd_as_1 = {13'b????????1???1};
	      wildcard bins bit_4_wr_as_0 = {13'b???????0????0};
	      wildcard bins bit_4_wr_as_1 = {13'b???????1????0};
	      wildcard bins bit_4_rd_as_0 = {13'b???????0????1};
	      wildcard bins bit_4_rd_as_1 = {13'b???????1????1};
	      wildcard bins bit_5_wr_as_0 = {13'b??????0?????0};
	      wildcard bins bit_5_wr_as_1 = {13'b??????1?????0};
	      wildcard bins bit_5_rd_as_0 = {13'b??????0?????1};
	      wildcard bins bit_5_rd_as_1 = {13'b??????1?????1};
	      wildcard bins bit_6_wr_as_0 = {13'b?????0??????0};
	      wildcard bins bit_6_wr_as_1 = {13'b?????1??????0};
	      wildcard bins bit_6_rd_as_0 = {13'b?????0??????1};
	      wildcard bins bit_6_rd_as_1 = {13'b?????1??????1};
	      wildcard bins bit_7_wr_as_0 = {13'b????0???????0};
	      wildcard bins bit_7_wr_as_1 = {13'b????1???????0};
	      wildcard bins bit_7_rd_as_0 = {13'b????0???????1};
	      wildcard bins bit_7_rd_as_1 = {13'b????1???????1};
	      wildcard bins bit_8_wr_as_0 = {13'b???0????????0};
	      wildcard bins bit_8_wr_as_1 = {13'b???1????????0};
	      wildcard bins bit_8_rd_as_0 = {13'b???0????????1};
	      wildcard bins bit_8_rd_as_1 = {13'b???1????????1};
	      wildcard bins bit_9_wr_as_0 = {13'b??0?????????0};
	      wildcard bins bit_9_wr_as_1 = {13'b??1?????????0};
	      wildcard bins bit_9_rd_as_0 = {13'b??0?????????1};
	      wildcard bins bit_9_rd_as_1 = {13'b??1?????????1};
	      wildcard bins bit_10_wr_as_0 = {13'b?0??????????0};
	      wildcard bins bit_10_wr_as_1 = {13'b?1??????????0};
	      wildcard bins bit_10_rd_as_0 = {13'b?0??????????1};
	      wildcard bins bit_10_rd_as_1 = {13'b?1??????????1};
	      wildcard bins bit_11_wr_as_0 = {13'b0???????????0};
	      wildcard bins bit_11_wr_as_1 = {13'b1???????????0};
	      wildcard bins bit_11_rd_as_0 = {13'b0???????????1};
	      wildcard bins bit_11_rd_as_1 = {13'b1???????????1};
	      option.weight = 48;
	   }
	   refresh_timer1_start_value_x32: coverpoint {m_data[27:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {13'b???????????00};
	      wildcard bins bit_0_wr_as_1 = {13'b???????????10};
	      wildcard bins bit_0_rd_as_0 = {13'b???????????01};
	      wildcard bins bit_0_rd_as_1 = {13'b???????????11};
	      wildcard bins bit_1_wr_as_0 = {13'b??????????0?0};
	      wildcard bins bit_1_wr_as_1 = {13'b??????????1?0};
	      wildcard bins bit_1_rd_as_0 = {13'b??????????0?1};
	      wildcard bins bit_1_rd_as_1 = {13'b??????????1?1};
	      wildcard bins bit_2_wr_as_0 = {13'b?????????0??0};
	      wildcard bins bit_2_wr_as_1 = {13'b?????????1??0};
	      wildcard bins bit_2_rd_as_0 = {13'b?????????0??1};
	      wildcard bins bit_2_rd_as_1 = {13'b?????????1??1};
	      wildcard bins bit_3_wr_as_0 = {13'b????????0???0};
	      wildcard bins bit_3_wr_as_1 = {13'b????????1???0};
	      wildcard bins bit_3_rd_as_0 = {13'b????????0???1};
	      wildcard bins bit_3_rd_as_1 = {13'b????????1???1};
	      wildcard bins bit_4_wr_as_0 = {13'b???????0????0};
	      wildcard bins bit_4_wr_as_1 = {13'b???????1????0};
	      wildcard bins bit_4_rd_as_0 = {13'b???????0????1};
	      wildcard bins bit_4_rd_as_1 = {13'b???????1????1};
	      wildcard bins bit_5_wr_as_0 = {13'b??????0?????0};
	      wildcard bins bit_5_wr_as_1 = {13'b??????1?????0};
	      wildcard bins bit_5_rd_as_0 = {13'b??????0?????1};
	      wildcard bins bit_5_rd_as_1 = {13'b??????1?????1};
	      wildcard bins bit_6_wr_as_0 = {13'b?????0??????0};
	      wildcard bins bit_6_wr_as_1 = {13'b?????1??????0};
	      wildcard bins bit_6_rd_as_0 = {13'b?????0??????1};
	      wildcard bins bit_6_rd_as_1 = {13'b?????1??????1};
	      wildcard bins bit_7_wr_as_0 = {13'b????0???????0};
	      wildcard bins bit_7_wr_as_1 = {13'b????1???????0};
	      wildcard bins bit_7_rd_as_0 = {13'b????0???????1};
	      wildcard bins bit_7_rd_as_1 = {13'b????1???????1};
	      wildcard bins bit_8_wr_as_0 = {13'b???0????????0};
	      wildcard bins bit_8_wr_as_1 = {13'b???1????????0};
	      wildcard bins bit_8_rd_as_0 = {13'b???0????????1};
	      wildcard bins bit_8_rd_as_1 = {13'b???1????????1};
	      wildcard bins bit_9_wr_as_0 = {13'b??0?????????0};
	      wildcard bins bit_9_wr_as_1 = {13'b??1?????????0};
	      wildcard bins bit_9_rd_as_0 = {13'b??0?????????1};
	      wildcard bins bit_9_rd_as_1 = {13'b??1?????????1};
	      wildcard bins bit_10_wr_as_0 = {13'b?0??????????0};
	      wildcard bins bit_10_wr_as_1 = {13'b?1??????????0};
	      wildcard bins bit_10_rd_as_0 = {13'b?0??????????1};
	      wildcard bins bit_10_rd_as_1 = {13'b?1??????????1};
	      wildcard bins bit_11_wr_as_0 = {13'b0???????????0};
	      wildcard bins bit_11_wr_as_1 = {13'b1???????????0};
	      wildcard bins bit_11_rd_as_0 = {13'b0???????????1};
	      wildcard bins bit_11_rd_as_1 = {13'b1???????????1};
	      option.weight = 48;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG4");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.refresh_timer0_start_value_x32 = uvm_reg_field::type_id::create("refresh_timer0_start_value_x32",,get_full_name());
      this.refresh_timer0_start_value_x32.configure(this, 12, 0, "RW", 0, 12'h0, 1, 0, 1);
      this.refresh_timer1_start_value_x32 = uvm_reg_field::type_id::create("refresh_timer1_start_value_x32",,get_full_name());
      this.refresh_timer1_start_value_x32.configure(this, 12, 16, "RW", 0, 12'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG4)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG4


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFMSET1TMG0 extends uvm_reg;
	rand uvm_reg_field t_rfmpb;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   t_rfmpb: coverpoint {m_data[11:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {13'b???????????00};
	      wildcard bins bit_0_wr_as_1 = {13'b???????????10};
	      wildcard bins bit_0_rd_as_0 = {13'b???????????01};
	      wildcard bins bit_0_rd_as_1 = {13'b???????????11};
	      wildcard bins bit_1_wr_as_0 = {13'b??????????0?0};
	      wildcard bins bit_1_wr_as_1 = {13'b??????????1?0};
	      wildcard bins bit_1_rd_as_0 = {13'b??????????0?1};
	      wildcard bins bit_1_rd_as_1 = {13'b??????????1?1};
	      wildcard bins bit_2_wr_as_0 = {13'b?????????0??0};
	      wildcard bins bit_2_wr_as_1 = {13'b?????????1??0};
	      wildcard bins bit_2_rd_as_0 = {13'b?????????0??1};
	      wildcard bins bit_2_rd_as_1 = {13'b?????????1??1};
	      wildcard bins bit_3_wr_as_0 = {13'b????????0???0};
	      wildcard bins bit_3_wr_as_1 = {13'b????????1???0};
	      wildcard bins bit_3_rd_as_0 = {13'b????????0???1};
	      wildcard bins bit_3_rd_as_1 = {13'b????????1???1};
	      wildcard bins bit_4_wr_as_0 = {13'b???????0????0};
	      wildcard bins bit_4_wr_as_1 = {13'b???????1????0};
	      wildcard bins bit_4_rd_as_0 = {13'b???????0????1};
	      wildcard bins bit_4_rd_as_1 = {13'b???????1????1};
	      wildcard bins bit_5_wr_as_0 = {13'b??????0?????0};
	      wildcard bins bit_5_wr_as_1 = {13'b??????1?????0};
	      wildcard bins bit_5_rd_as_0 = {13'b??????0?????1};
	      wildcard bins bit_5_rd_as_1 = {13'b??????1?????1};
	      wildcard bins bit_6_wr_as_0 = {13'b?????0??????0};
	      wildcard bins bit_6_wr_as_1 = {13'b?????1??????0};
	      wildcard bins bit_6_rd_as_0 = {13'b?????0??????1};
	      wildcard bins bit_6_rd_as_1 = {13'b?????1??????1};
	      wildcard bins bit_7_wr_as_0 = {13'b????0???????0};
	      wildcard bins bit_7_wr_as_1 = {13'b????1???????0};
	      wildcard bins bit_7_rd_as_0 = {13'b????0???????1};
	      wildcard bins bit_7_rd_as_1 = {13'b????1???????1};
	      wildcard bins bit_8_wr_as_0 = {13'b???0????????0};
	      wildcard bins bit_8_wr_as_1 = {13'b???1????????0};
	      wildcard bins bit_8_rd_as_0 = {13'b???0????????1};
	      wildcard bins bit_8_rd_as_1 = {13'b???1????????1};
	      wildcard bins bit_9_wr_as_0 = {13'b??0?????????0};
	      wildcard bins bit_9_wr_as_1 = {13'b??1?????????0};
	      wildcard bins bit_9_rd_as_0 = {13'b??0?????????1};
	      wildcard bins bit_9_rd_as_1 = {13'b??1?????????1};
	      wildcard bins bit_10_wr_as_0 = {13'b?0??????????0};
	      wildcard bins bit_10_wr_as_1 = {13'b?1??????????0};
	      wildcard bins bit_10_rd_as_0 = {13'b?0??????????1};
	      wildcard bins bit_10_rd_as_1 = {13'b?1??????????1};
	      wildcard bins bit_11_wr_as_0 = {13'b0???????????0};
	      wildcard bins bit_11_wr_as_1 = {13'b1???????????0};
	      wildcard bins bit_11_rd_as_0 = {13'b0???????????1};
	      wildcard bins bit_11_rd_as_1 = {13'b1???????????1};
	      option.weight = 48;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_RFMSET1TMG0");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.t_rfmpb = uvm_reg_field::type_id::create("t_rfmpb",,get_full_name());
      this.t_rfmpb.configure(this, 12, 0, "RW", 0, 12'h8c, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFMSET1TMG0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFMSET1TMG0


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_ZQSET1TMG0 extends uvm_reg;
	rand uvm_reg_field t_zq_long_nop;
	rand uvm_reg_field t_zq_short_nop;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   t_zq_long_nop: coverpoint {m_data[13:0], m_is_read} iff(m_be) {
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
	   t_zq_short_nop: coverpoint {m_data[25:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_ZQSET1TMG0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.t_zq_long_nop = uvm_reg_field::type_id::create("t_zq_long_nop",,get_full_name());
      this.t_zq_long_nop.configure(this, 14, 0, "RW", 0, 14'h200, 1, 0, 1);
      this.t_zq_short_nop = uvm_reg_field::type_id::create("t_zq_short_nop",,get_full_name());
      this.t_zq_short_nop.configure(this, 10, 16, "RW", 0, 10'h40, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_ZQSET1TMG0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_ZQSET1TMG0


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_ZQSET1TMG1 extends uvm_reg;
	rand uvm_reg_field t_zq_short_interval_x1024;
	rand uvm_reg_field t_zq_reset_nop;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   t_zq_short_interval_x1024: coverpoint {m_data[19:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {21'b???????????????????00};
	      wildcard bins bit_0_wr_as_1 = {21'b???????????????????10};
	      wildcard bins bit_0_rd_as_0 = {21'b???????????????????01};
	      wildcard bins bit_0_rd_as_1 = {21'b???????????????????11};
	      wildcard bins bit_1_wr_as_0 = {21'b??????????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {21'b??????????????????1?0};
	      wildcard bins bit_1_rd_as_0 = {21'b??????????????????0?1};
	      wildcard bins bit_1_rd_as_1 = {21'b??????????????????1?1};
	      wildcard bins bit_2_wr_as_0 = {21'b?????????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {21'b?????????????????1??0};
	      wildcard bins bit_2_rd_as_0 = {21'b?????????????????0??1};
	      wildcard bins bit_2_rd_as_1 = {21'b?????????????????1??1};
	      wildcard bins bit_3_wr_as_0 = {21'b????????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {21'b????????????????1???0};
	      wildcard bins bit_3_rd_as_0 = {21'b????????????????0???1};
	      wildcard bins bit_3_rd_as_1 = {21'b????????????????1???1};
	      wildcard bins bit_4_wr_as_0 = {21'b???????????????0????0};
	      wildcard bins bit_4_wr_as_1 = {21'b???????????????1????0};
	      wildcard bins bit_4_rd_as_0 = {21'b???????????????0????1};
	      wildcard bins bit_4_rd_as_1 = {21'b???????????????1????1};
	      wildcard bins bit_5_wr_as_0 = {21'b??????????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {21'b??????????????1?????0};
	      wildcard bins bit_5_rd_as_0 = {21'b??????????????0?????1};
	      wildcard bins bit_5_rd_as_1 = {21'b??????????????1?????1};
	      wildcard bins bit_6_wr_as_0 = {21'b?????????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {21'b?????????????1??????0};
	      wildcard bins bit_6_rd_as_0 = {21'b?????????????0??????1};
	      wildcard bins bit_6_rd_as_1 = {21'b?????????????1??????1};
	      wildcard bins bit_7_wr_as_0 = {21'b????????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {21'b????????????1???????0};
	      wildcard bins bit_7_rd_as_0 = {21'b????????????0???????1};
	      wildcard bins bit_7_rd_as_1 = {21'b????????????1???????1};
	      wildcard bins bit_8_wr_as_0 = {21'b???????????0????????0};
	      wildcard bins bit_8_wr_as_1 = {21'b???????????1????????0};
	      wildcard bins bit_8_rd_as_0 = {21'b???????????0????????1};
	      wildcard bins bit_8_rd_as_1 = {21'b???????????1????????1};
	      wildcard bins bit_9_wr_as_0 = {21'b??????????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {21'b??????????1?????????0};
	      wildcard bins bit_9_rd_as_0 = {21'b??????????0?????????1};
	      wildcard bins bit_9_rd_as_1 = {21'b??????????1?????????1};
	      wildcard bins bit_10_wr_as_0 = {21'b?????????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {21'b?????????1??????????0};
	      wildcard bins bit_10_rd_as_0 = {21'b?????????0??????????1};
	      wildcard bins bit_10_rd_as_1 = {21'b?????????1??????????1};
	      wildcard bins bit_11_wr_as_0 = {21'b????????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {21'b????????1???????????0};
	      wildcard bins bit_11_rd_as_0 = {21'b????????0???????????1};
	      wildcard bins bit_11_rd_as_1 = {21'b????????1???????????1};
	      wildcard bins bit_12_wr_as_0 = {21'b???????0????????????0};
	      wildcard bins bit_12_wr_as_1 = {21'b???????1????????????0};
	      wildcard bins bit_12_rd_as_0 = {21'b???????0????????????1};
	      wildcard bins bit_12_rd_as_1 = {21'b???????1????????????1};
	      wildcard bins bit_13_wr_as_0 = {21'b??????0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {21'b??????1?????????????0};
	      wildcard bins bit_13_rd_as_0 = {21'b??????0?????????????1};
	      wildcard bins bit_13_rd_as_1 = {21'b??????1?????????????1};
	      wildcard bins bit_14_wr_as_0 = {21'b?????0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {21'b?????1??????????????0};
	      wildcard bins bit_14_rd_as_0 = {21'b?????0??????????????1};
	      wildcard bins bit_14_rd_as_1 = {21'b?????1??????????????1};
	      wildcard bins bit_15_wr_as_0 = {21'b????0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {21'b????1???????????????0};
	      wildcard bins bit_15_rd_as_0 = {21'b????0???????????????1};
	      wildcard bins bit_15_rd_as_1 = {21'b????1???????????????1};
	      wildcard bins bit_16_wr_as_0 = {21'b???0????????????????0};
	      wildcard bins bit_16_wr_as_1 = {21'b???1????????????????0};
	      wildcard bins bit_16_rd_as_0 = {21'b???0????????????????1};
	      wildcard bins bit_16_rd_as_1 = {21'b???1????????????????1};
	      wildcard bins bit_17_wr_as_0 = {21'b??0?????????????????0};
	      wildcard bins bit_17_wr_as_1 = {21'b??1?????????????????0};
	      wildcard bins bit_17_rd_as_0 = {21'b??0?????????????????1};
	      wildcard bins bit_17_rd_as_1 = {21'b??1?????????????????1};
	      wildcard bins bit_18_wr_as_0 = {21'b?0??????????????????0};
	      wildcard bins bit_18_wr_as_1 = {21'b?1??????????????????0};
	      wildcard bins bit_18_rd_as_0 = {21'b?0??????????????????1};
	      wildcard bins bit_18_rd_as_1 = {21'b?1??????????????????1};
	      wildcard bins bit_19_wr_as_0 = {21'b0???????????????????0};
	      wildcard bins bit_19_wr_as_1 = {21'b1???????????????????0};
	      wildcard bins bit_19_rd_as_0 = {21'b0???????????????????1};
	      wildcard bins bit_19_rd_as_1 = {21'b1???????????????????1};
	      option.weight = 80;
	   }
	   t_zq_reset_nop: coverpoint {m_data[29:20], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_ZQSET1TMG1");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.t_zq_short_interval_x1024 = uvm_reg_field::type_id::create("t_zq_short_interval_x1024",,get_full_name());
      this.t_zq_short_interval_x1024.configure(this, 20, 0, "RW", 0, 20'h100, 1, 0, 0);
      this.t_zq_reset_nop = uvm_reg_field::type_id::create("t_zq_reset_nop",,get_full_name());
      this.t_zq_reset_nop.configure(this, 10, 20, "RW", 0, 10'h20, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_ZQSET1TMG1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_ZQSET1TMG1


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_ZQSET1TMG2 extends uvm_reg;
	rand uvm_reg_field t_zq_stop;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   t_zq_stop: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_ZQSET1TMG2");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.t_zq_stop = uvm_reg_field::type_id::create("t_zq_stop",,get_full_name());
      this.t_zq_stop.configure(this, 7, 0, "RW", 0, 7'h18, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_ZQSET1TMG2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_ZQSET1TMG2


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DQSOSCCTL0 extends uvm_reg;
	rand uvm_reg_field dqsosc_enable;
	rand uvm_reg_field dqsosc_interval_unit;
	rand uvm_reg_field dqsosc_interval;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dqsosc_enable: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dqsosc_interval_unit: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dqsosc_interval: coverpoint {m_data[15:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {13'b???????????00};
	      wildcard bins bit_0_wr_as_1 = {13'b???????????10};
	      wildcard bins bit_0_rd_as_0 = {13'b???????????01};
	      wildcard bins bit_0_rd_as_1 = {13'b???????????11};
	      wildcard bins bit_1_wr_as_0 = {13'b??????????0?0};
	      wildcard bins bit_1_wr_as_1 = {13'b??????????1?0};
	      wildcard bins bit_1_rd_as_0 = {13'b??????????0?1};
	      wildcard bins bit_1_rd_as_1 = {13'b??????????1?1};
	      wildcard bins bit_2_wr_as_0 = {13'b?????????0??0};
	      wildcard bins bit_2_wr_as_1 = {13'b?????????1??0};
	      wildcard bins bit_2_rd_as_0 = {13'b?????????0??1};
	      wildcard bins bit_2_rd_as_1 = {13'b?????????1??1};
	      wildcard bins bit_3_wr_as_0 = {13'b????????0???0};
	      wildcard bins bit_3_wr_as_1 = {13'b????????1???0};
	      wildcard bins bit_3_rd_as_0 = {13'b????????0???1};
	      wildcard bins bit_3_rd_as_1 = {13'b????????1???1};
	      wildcard bins bit_4_wr_as_0 = {13'b???????0????0};
	      wildcard bins bit_4_wr_as_1 = {13'b???????1????0};
	      wildcard bins bit_4_rd_as_0 = {13'b???????0????1};
	      wildcard bins bit_4_rd_as_1 = {13'b???????1????1};
	      wildcard bins bit_5_wr_as_0 = {13'b??????0?????0};
	      wildcard bins bit_5_wr_as_1 = {13'b??????1?????0};
	      wildcard bins bit_5_rd_as_0 = {13'b??????0?????1};
	      wildcard bins bit_5_rd_as_1 = {13'b??????1?????1};
	      wildcard bins bit_6_wr_as_0 = {13'b?????0??????0};
	      wildcard bins bit_6_wr_as_1 = {13'b?????1??????0};
	      wildcard bins bit_6_rd_as_0 = {13'b?????0??????1};
	      wildcard bins bit_6_rd_as_1 = {13'b?????1??????1};
	      wildcard bins bit_7_wr_as_0 = {13'b????0???????0};
	      wildcard bins bit_7_wr_as_1 = {13'b????1???????0};
	      wildcard bins bit_7_rd_as_0 = {13'b????0???????1};
	      wildcard bins bit_7_rd_as_1 = {13'b????1???????1};
	      wildcard bins bit_8_wr_as_0 = {13'b???0????????0};
	      wildcard bins bit_8_wr_as_1 = {13'b???1????????0};
	      wildcard bins bit_8_rd_as_0 = {13'b???0????????1};
	      wildcard bins bit_8_rd_as_1 = {13'b???1????????1};
	      wildcard bins bit_9_wr_as_0 = {13'b??0?????????0};
	      wildcard bins bit_9_wr_as_1 = {13'b??1?????????0};
	      wildcard bins bit_9_rd_as_0 = {13'b??0?????????1};
	      wildcard bins bit_9_rd_as_1 = {13'b??1?????????1};
	      wildcard bins bit_10_wr_as_0 = {13'b?0??????????0};
	      wildcard bins bit_10_wr_as_1 = {13'b?1??????????0};
	      wildcard bins bit_10_rd_as_0 = {13'b?0??????????1};
	      wildcard bins bit_10_rd_as_1 = {13'b?1??????????1};
	      wildcard bins bit_11_wr_as_0 = {13'b0???????????0};
	      wildcard bins bit_11_wr_as_1 = {13'b1???????????0};
	      wildcard bins bit_11_rd_as_0 = {13'b0???????????1};
	      wildcard bins bit_11_rd_as_1 = {13'b1???????????1};
	      option.weight = 48;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DQSOSCCTL0");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dqsosc_enable = uvm_reg_field::type_id::create("dqsosc_enable",,get_full_name());
      this.dqsosc_enable.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.dqsosc_interval_unit = uvm_reg_field::type_id::create("dqsosc_interval_unit",,get_full_name());
      this.dqsosc_interval_unit.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
      this.dqsosc_interval = uvm_reg_field::type_id::create("dqsosc_interval",,get_full_name());
      this.dqsosc_interval.configure(this, 12, 4, "RW", 0, 12'h7, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DQSOSCCTL0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DQSOSCCTL0


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DERATEINT extends uvm_reg;
	rand uvm_reg_field mr4_read_interval;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   mr4_read_interval: coverpoint {m_data[31:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {33'b???????????????????????????????00};
	      wildcard bins bit_0_wr_as_1 = {33'b???????????????????????????????10};
	      wildcard bins bit_0_rd_as_0 = {33'b???????????????????????????????01};
	      wildcard bins bit_0_rd_as_1 = {33'b???????????????????????????????11};
	      wildcard bins bit_1_wr_as_0 = {33'b??????????????????????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {33'b??????????????????????????????1?0};
	      wildcard bins bit_1_rd_as_0 = {33'b??????????????????????????????0?1};
	      wildcard bins bit_1_rd_as_1 = {33'b??????????????????????????????1?1};
	      wildcard bins bit_2_wr_as_0 = {33'b?????????????????????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {33'b?????????????????????????????1??0};
	      wildcard bins bit_2_rd_as_0 = {33'b?????????????????????????????0??1};
	      wildcard bins bit_2_rd_as_1 = {33'b?????????????????????????????1??1};
	      wildcard bins bit_3_wr_as_0 = {33'b????????????????????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {33'b????????????????????????????1???0};
	      wildcard bins bit_3_rd_as_0 = {33'b????????????????????????????0???1};
	      wildcard bins bit_3_rd_as_1 = {33'b????????????????????????????1???1};
	      wildcard bins bit_4_wr_as_0 = {33'b???????????????????????????0????0};
	      wildcard bins bit_4_wr_as_1 = {33'b???????????????????????????1????0};
	      wildcard bins bit_4_rd_as_0 = {33'b???????????????????????????0????1};
	      wildcard bins bit_4_rd_as_1 = {33'b???????????????????????????1????1};
	      wildcard bins bit_5_wr_as_0 = {33'b??????????????????????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {33'b??????????????????????????1?????0};
	      wildcard bins bit_5_rd_as_0 = {33'b??????????????????????????0?????1};
	      wildcard bins bit_5_rd_as_1 = {33'b??????????????????????????1?????1};
	      wildcard bins bit_6_wr_as_0 = {33'b?????????????????????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {33'b?????????????????????????1??????0};
	      wildcard bins bit_6_rd_as_0 = {33'b?????????????????????????0??????1};
	      wildcard bins bit_6_rd_as_1 = {33'b?????????????????????????1??????1};
	      wildcard bins bit_7_wr_as_0 = {33'b????????????????????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {33'b????????????????????????1???????0};
	      wildcard bins bit_7_rd_as_0 = {33'b????????????????????????0???????1};
	      wildcard bins bit_7_rd_as_1 = {33'b????????????????????????1???????1};
	      wildcard bins bit_8_wr_as_0 = {33'b???????????????????????0????????0};
	      wildcard bins bit_8_wr_as_1 = {33'b???????????????????????1????????0};
	      wildcard bins bit_8_rd_as_0 = {33'b???????????????????????0????????1};
	      wildcard bins bit_8_rd_as_1 = {33'b???????????????????????1????????1};
	      wildcard bins bit_9_wr_as_0 = {33'b??????????????????????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {33'b??????????????????????1?????????0};
	      wildcard bins bit_9_rd_as_0 = {33'b??????????????????????0?????????1};
	      wildcard bins bit_9_rd_as_1 = {33'b??????????????????????1?????????1};
	      wildcard bins bit_10_wr_as_0 = {33'b?????????????????????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {33'b?????????????????????1??????????0};
	      wildcard bins bit_10_rd_as_0 = {33'b?????????????????????0??????????1};
	      wildcard bins bit_10_rd_as_1 = {33'b?????????????????????1??????????1};
	      wildcard bins bit_11_wr_as_0 = {33'b????????????????????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {33'b????????????????????1???????????0};
	      wildcard bins bit_11_rd_as_0 = {33'b????????????????????0???????????1};
	      wildcard bins bit_11_rd_as_1 = {33'b????????????????????1???????????1};
	      wildcard bins bit_12_wr_as_0 = {33'b???????????????????0????????????0};
	      wildcard bins bit_12_wr_as_1 = {33'b???????????????????1????????????0};
	      wildcard bins bit_12_rd_as_0 = {33'b???????????????????0????????????1};
	      wildcard bins bit_12_rd_as_1 = {33'b???????????????????1????????????1};
	      wildcard bins bit_13_wr_as_0 = {33'b??????????????????0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {33'b??????????????????1?????????????0};
	      wildcard bins bit_13_rd_as_0 = {33'b??????????????????0?????????????1};
	      wildcard bins bit_13_rd_as_1 = {33'b??????????????????1?????????????1};
	      wildcard bins bit_14_wr_as_0 = {33'b?????????????????0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {33'b?????????????????1??????????????0};
	      wildcard bins bit_14_rd_as_0 = {33'b?????????????????0??????????????1};
	      wildcard bins bit_14_rd_as_1 = {33'b?????????????????1??????????????1};
	      wildcard bins bit_15_wr_as_0 = {33'b????????????????0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {33'b????????????????1???????????????0};
	      wildcard bins bit_15_rd_as_0 = {33'b????????????????0???????????????1};
	      wildcard bins bit_15_rd_as_1 = {33'b????????????????1???????????????1};
	      wildcard bins bit_16_wr_as_0 = {33'b???????????????0????????????????0};
	      wildcard bins bit_16_wr_as_1 = {33'b???????????????1????????????????0};
	      wildcard bins bit_16_rd_as_0 = {33'b???????????????0????????????????1};
	      wildcard bins bit_16_rd_as_1 = {33'b???????????????1????????????????1};
	      wildcard bins bit_17_wr_as_0 = {33'b??????????????0?????????????????0};
	      wildcard bins bit_17_wr_as_1 = {33'b??????????????1?????????????????0};
	      wildcard bins bit_17_rd_as_0 = {33'b??????????????0?????????????????1};
	      wildcard bins bit_17_rd_as_1 = {33'b??????????????1?????????????????1};
	      wildcard bins bit_18_wr_as_0 = {33'b?????????????0??????????????????0};
	      wildcard bins bit_18_wr_as_1 = {33'b?????????????1??????????????????0};
	      wildcard bins bit_18_rd_as_0 = {33'b?????????????0??????????????????1};
	      wildcard bins bit_18_rd_as_1 = {33'b?????????????1??????????????????1};
	      wildcard bins bit_19_wr_as_0 = {33'b????????????0???????????????????0};
	      wildcard bins bit_19_wr_as_1 = {33'b????????????1???????????????????0};
	      wildcard bins bit_19_rd_as_0 = {33'b????????????0???????????????????1};
	      wildcard bins bit_19_rd_as_1 = {33'b????????????1???????????????????1};
	      wildcard bins bit_20_wr_as_0 = {33'b???????????0????????????????????0};
	      wildcard bins bit_20_wr_as_1 = {33'b???????????1????????????????????0};
	      wildcard bins bit_20_rd_as_0 = {33'b???????????0????????????????????1};
	      wildcard bins bit_20_rd_as_1 = {33'b???????????1????????????????????1};
	      wildcard bins bit_21_wr_as_0 = {33'b??????????0?????????????????????0};
	      wildcard bins bit_21_wr_as_1 = {33'b??????????1?????????????????????0};
	      wildcard bins bit_21_rd_as_0 = {33'b??????????0?????????????????????1};
	      wildcard bins bit_21_rd_as_1 = {33'b??????????1?????????????????????1};
	      wildcard bins bit_22_wr_as_0 = {33'b?????????0??????????????????????0};
	      wildcard bins bit_22_wr_as_1 = {33'b?????????1??????????????????????0};
	      wildcard bins bit_22_rd_as_0 = {33'b?????????0??????????????????????1};
	      wildcard bins bit_22_rd_as_1 = {33'b?????????1??????????????????????1};
	      wildcard bins bit_23_wr_as_0 = {33'b????????0???????????????????????0};
	      wildcard bins bit_23_wr_as_1 = {33'b????????1???????????????????????0};
	      wildcard bins bit_23_rd_as_0 = {33'b????????0???????????????????????1};
	      wildcard bins bit_23_rd_as_1 = {33'b????????1???????????????????????1};
	      wildcard bins bit_24_wr_as_0 = {33'b???????0????????????????????????0};
	      wildcard bins bit_24_wr_as_1 = {33'b???????1????????????????????????0};
	      wildcard bins bit_24_rd_as_0 = {33'b???????0????????????????????????1};
	      wildcard bins bit_24_rd_as_1 = {33'b???????1????????????????????????1};
	      wildcard bins bit_25_wr_as_0 = {33'b??????0?????????????????????????0};
	      wildcard bins bit_25_wr_as_1 = {33'b??????1?????????????????????????0};
	      wildcard bins bit_25_rd_as_0 = {33'b??????0?????????????????????????1};
	      wildcard bins bit_25_rd_as_1 = {33'b??????1?????????????????????????1};
	      wildcard bins bit_26_wr_as_0 = {33'b?????0??????????????????????????0};
	      wildcard bins bit_26_wr_as_1 = {33'b?????1??????????????????????????0};
	      wildcard bins bit_26_rd_as_0 = {33'b?????0??????????????????????????1};
	      wildcard bins bit_26_rd_as_1 = {33'b?????1??????????????????????????1};
	      wildcard bins bit_27_wr_as_0 = {33'b????0???????????????????????????0};
	      wildcard bins bit_27_wr_as_1 = {33'b????1???????????????????????????0};
	      wildcard bins bit_27_rd_as_0 = {33'b????0???????????????????????????1};
	      wildcard bins bit_27_rd_as_1 = {33'b????1???????????????????????????1};
	      wildcard bins bit_28_wr_as_0 = {33'b???0????????????????????????????0};
	      wildcard bins bit_28_wr_as_1 = {33'b???1????????????????????????????0};
	      wildcard bins bit_28_rd_as_0 = {33'b???0????????????????????????????1};
	      wildcard bins bit_28_rd_as_1 = {33'b???1????????????????????????????1};
	      wildcard bins bit_29_wr_as_0 = {33'b??0?????????????????????????????0};
	      wildcard bins bit_29_wr_as_1 = {33'b??1?????????????????????????????0};
	      wildcard bins bit_29_rd_as_0 = {33'b??0?????????????????????????????1};
	      wildcard bins bit_29_rd_as_1 = {33'b??1?????????????????????????????1};
	      wildcard bins bit_30_wr_as_0 = {33'b?0??????????????????????????????0};
	      wildcard bins bit_30_wr_as_1 = {33'b?1??????????????????????????????0};
	      wildcard bins bit_30_rd_as_0 = {33'b?0??????????????????????????????1};
	      wildcard bins bit_30_rd_as_1 = {33'b?1??????????????????????????????1};
	      wildcard bins bit_31_wr_as_0 = {33'b0???????????????????????????????0};
	      wildcard bins bit_31_wr_as_1 = {33'b1???????????????????????????????0};
	      wildcard bins bit_31_rd_as_0 = {33'b0???????????????????????????????1};
	      wildcard bins bit_31_rd_as_1 = {33'b1???????????????????????????????1};
	      option.weight = 128;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DERATEINT");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.mr4_read_interval = uvm_reg_field::type_id::create("mr4_read_interval",,get_full_name());
      this.mr4_read_interval.configure(this, 32, 0, "RW", 1, 32'h800000, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DERATEINT)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DERATEINT


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DERATEVAL0 extends uvm_reg;
	rand uvm_reg_field derated_t_rrd;
	rand uvm_reg_field derated_t_rp;
	rand uvm_reg_field derated_t_ras_min;
	rand uvm_reg_field derated_t_rcd;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   derated_t_rrd: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
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
	   derated_t_rp: coverpoint {m_data[14:8], m_is_read} iff(m_be) {
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
	   derated_t_ras_min: coverpoint {m_data[23:16], m_is_read} iff(m_be) {
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
	   derated_t_rcd: coverpoint {m_data[31:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DERATEVAL0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.derated_t_rrd = uvm_reg_field::type_id::create("derated_t_rrd",,get_full_name());
      this.derated_t_rrd.configure(this, 6, 0, "RW", 1, 6'h4, 1, 0, 1);
      this.derated_t_rp = uvm_reg_field::type_id::create("derated_t_rp",,get_full_name());
      this.derated_t_rp.configure(this, 7, 8, "RW", 1, 7'h5, 1, 0, 1);
      this.derated_t_ras_min = uvm_reg_field::type_id::create("derated_t_ras_min",,get_full_name());
      this.derated_t_ras_min.configure(this, 8, 16, "RW", 1, 8'hf, 1, 0, 1);
      this.derated_t_rcd = uvm_reg_field::type_id::create("derated_t_rcd",,get_full_name());
      this.derated_t_rcd.configure(this, 8, 24, "RW", 1, 8'h5, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DERATEVAL0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DERATEVAL0


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DERATEVAL1 extends uvm_reg;
	rand uvm_reg_field derated_t_rc;
	rand uvm_reg_field derated_t_rcd_write;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   derated_t_rc: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	   derated_t_rcd_write: coverpoint {m_data[15:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DERATEVAL1");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.derated_t_rc = uvm_reg_field::type_id::create("derated_t_rc",,get_full_name());
      this.derated_t_rc.configure(this, 8, 0, "RW", 1, 8'h14, 1, 0, 1);
      this.derated_t_rcd_write = uvm_reg_field::type_id::create("derated_t_rcd_write",,get_full_name());
      this.derated_t_rcd_write.configure(this, 8, 8, "RW", 1, 8'h5, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DERATEVAL1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DERATEVAL1


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_HWLPTMG0 extends uvm_reg;
	rand uvm_reg_field hw_lp_idle_x32;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   hw_lp_idle_x32: coverpoint {m_data[27:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {13'b???????????00};
	      wildcard bins bit_0_wr_as_1 = {13'b???????????10};
	      wildcard bins bit_0_rd_as_0 = {13'b???????????01};
	      wildcard bins bit_0_rd_as_1 = {13'b???????????11};
	      wildcard bins bit_1_wr_as_0 = {13'b??????????0?0};
	      wildcard bins bit_1_wr_as_1 = {13'b??????????1?0};
	      wildcard bins bit_1_rd_as_0 = {13'b??????????0?1};
	      wildcard bins bit_1_rd_as_1 = {13'b??????????1?1};
	      wildcard bins bit_2_wr_as_0 = {13'b?????????0??0};
	      wildcard bins bit_2_wr_as_1 = {13'b?????????1??0};
	      wildcard bins bit_2_rd_as_0 = {13'b?????????0??1};
	      wildcard bins bit_2_rd_as_1 = {13'b?????????1??1};
	      wildcard bins bit_3_wr_as_0 = {13'b????????0???0};
	      wildcard bins bit_3_wr_as_1 = {13'b????????1???0};
	      wildcard bins bit_3_rd_as_0 = {13'b????????0???1};
	      wildcard bins bit_3_rd_as_1 = {13'b????????1???1};
	      wildcard bins bit_4_wr_as_0 = {13'b???????0????0};
	      wildcard bins bit_4_wr_as_1 = {13'b???????1????0};
	      wildcard bins bit_4_rd_as_0 = {13'b???????0????1};
	      wildcard bins bit_4_rd_as_1 = {13'b???????1????1};
	      wildcard bins bit_5_wr_as_0 = {13'b??????0?????0};
	      wildcard bins bit_5_wr_as_1 = {13'b??????1?????0};
	      wildcard bins bit_5_rd_as_0 = {13'b??????0?????1};
	      wildcard bins bit_5_rd_as_1 = {13'b??????1?????1};
	      wildcard bins bit_6_wr_as_0 = {13'b?????0??????0};
	      wildcard bins bit_6_wr_as_1 = {13'b?????1??????0};
	      wildcard bins bit_6_rd_as_0 = {13'b?????0??????1};
	      wildcard bins bit_6_rd_as_1 = {13'b?????1??????1};
	      wildcard bins bit_7_wr_as_0 = {13'b????0???????0};
	      wildcard bins bit_7_wr_as_1 = {13'b????1???????0};
	      wildcard bins bit_7_rd_as_0 = {13'b????0???????1};
	      wildcard bins bit_7_rd_as_1 = {13'b????1???????1};
	      wildcard bins bit_8_wr_as_0 = {13'b???0????????0};
	      wildcard bins bit_8_wr_as_1 = {13'b???1????????0};
	      wildcard bins bit_8_rd_as_0 = {13'b???0????????1};
	      wildcard bins bit_8_rd_as_1 = {13'b???1????????1};
	      wildcard bins bit_9_wr_as_0 = {13'b??0?????????0};
	      wildcard bins bit_9_wr_as_1 = {13'b??1?????????0};
	      wildcard bins bit_9_rd_as_0 = {13'b??0?????????1};
	      wildcard bins bit_9_rd_as_1 = {13'b??1?????????1};
	      wildcard bins bit_10_wr_as_0 = {13'b?0??????????0};
	      wildcard bins bit_10_wr_as_1 = {13'b?1??????????0};
	      wildcard bins bit_10_rd_as_0 = {13'b?0??????????1};
	      wildcard bins bit_10_rd_as_1 = {13'b?1??????????1};
	      wildcard bins bit_11_wr_as_0 = {13'b0???????????0};
	      wildcard bins bit_11_wr_as_1 = {13'b1???????????0};
	      wildcard bins bit_11_rd_as_0 = {13'b0???????????1};
	      wildcard bins bit_11_rd_as_1 = {13'b1???????????1};
	      option.weight = 48;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_HWLPTMG0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.hw_lp_idle_x32 = uvm_reg_field::type_id::create("hw_lp_idle_x32",,get_full_name());
      this.hw_lp_idle_x32.configure(this, 12, 16, "RW", 1, 12'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_HWLPTMG0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_HWLPTMG0


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DVFSCTL0 extends uvm_reg;
	rand uvm_reg_field dvfsq_enable;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dvfsq_enable: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DVFSCTL0");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dvfsq_enable = uvm_reg_field::type_id::create("dvfsq_enable",,get_full_name());
      this.dvfsq_enable.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DVFSCTL0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DVFSCTL0


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_SCHEDTMG0 extends uvm_reg;
	rand uvm_reg_field pageclose_timer;
	rand uvm_reg_field rdwr_idle_gap;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   pageclose_timer: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	   rdwr_idle_gap: coverpoint {m_data[14:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_SCHEDTMG0");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.pageclose_timer = uvm_reg_field::type_id::create("pageclose_timer",,get_full_name());
      this.pageclose_timer.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
      this.rdwr_idle_gap = uvm_reg_field::type_id::create("rdwr_idle_gap",,get_full_name());
      this.rdwr_idle_gap.configure(this, 7, 8, "RW", 0, 7'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_SCHEDTMG0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_SCHEDTMG0


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_PERFHPR1 extends uvm_reg;
	rand uvm_reg_field hpr_max_starve;
	rand uvm_reg_field hpr_xact_run_length;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   hpr_max_starve: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	   hpr_xact_run_length: coverpoint {m_data[31:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_PERFHPR1");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.hpr_max_starve = uvm_reg_field::type_id::create("hpr_max_starve",,get_full_name());
      this.hpr_max_starve.configure(this, 16, 0, "RW", 1, 16'h1, 1, 0, 1);
      this.hpr_xact_run_length = uvm_reg_field::type_id::create("hpr_xact_run_length",,get_full_name());
      this.hpr_xact_run_length.configure(this, 8, 24, "RW", 1, 8'hf, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_PERFHPR1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_PERFHPR1


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_PERFLPR1 extends uvm_reg;
	rand uvm_reg_field lpr_max_starve;
	rand uvm_reg_field lpr_xact_run_length;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   lpr_max_starve: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	   lpr_xact_run_length: coverpoint {m_data[31:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_PERFLPR1");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.lpr_max_starve = uvm_reg_field::type_id::create("lpr_max_starve",,get_full_name());
      this.lpr_max_starve.configure(this, 16, 0, "RW", 1, 16'h7f, 1, 0, 1);
      this.lpr_xact_run_length = uvm_reg_field::type_id::create("lpr_xact_run_length",,get_full_name());
      this.lpr_xact_run_length.configure(this, 8, 24, "RW", 1, 8'hf, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_PERFLPR1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_PERFLPR1


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_PERFWR1 extends uvm_reg;
	rand uvm_reg_field w_max_starve;
	rand uvm_reg_field w_xact_run_length;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   w_max_starve: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	   w_xact_run_length: coverpoint {m_data[31:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_PERFWR1");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.w_max_starve = uvm_reg_field::type_id::create("w_max_starve",,get_full_name());
      this.w_max_starve.configure(this, 16, 0, "RW", 1, 16'h7f, 1, 0, 1);
      this.w_xact_run_length = uvm_reg_field::type_id::create("w_xact_run_length",,get_full_name());
      this.w_xact_run_length.configure(this, 8, 24, "RW", 1, 8'hf, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_PERFWR1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_PERFWR1


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_TMGCFG extends uvm_reg;
	rand uvm_reg_field frequency_ratio;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   frequency_ratio: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_TMGCFG");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.frequency_ratio = uvm_reg_field::type_id::create("frequency_ratio",,get_full_name());
      this.frequency_ratio.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_TMGCFG)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_TMGCFG


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RANKTMG0 extends uvm_reg;
	rand uvm_reg_field diff_rank_rd_gap;
	rand uvm_reg_field diff_rank_wr_gap;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   diff_rank_rd_gap: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	   diff_rank_wr_gap: coverpoint {m_data[15:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_RANKTMG0");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.diff_rank_rd_gap = uvm_reg_field::type_id::create("diff_rank_rd_gap",,get_full_name());
      this.diff_rank_rd_gap.configure(this, 8, 0, "RW", 1, 8'h6, 1, 0, 1);
      this.diff_rank_wr_gap = uvm_reg_field::type_id::create("diff_rank_wr_gap",,get_full_name());
      this.diff_rank_wr_gap.configure(this, 8, 8, "RW", 1, 8'h6, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RANKTMG0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RANKTMG0


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RANKTMG1 extends uvm_reg;
	rand uvm_reg_field wr2rd_dr;
	rand uvm_reg_field rd2wr_dr;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   wr2rd_dr: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	   rd2wr_dr: coverpoint {m_data[15:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_RANKTMG1");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.wr2rd_dr = uvm_reg_field::type_id::create("wr2rd_dr",,get_full_name());
      this.wr2rd_dr.configure(this, 8, 0, "RW", 1, 8'hf, 1, 0, 1);
      this.rd2wr_dr = uvm_reg_field::type_id::create("rd2wr_dr",,get_full_name());
      this.rd2wr_dr.configure(this, 8, 8, "RW", 1, 8'hf, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RANKTMG1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RANKTMG1


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_PWRTMG extends uvm_reg;
	rand uvm_reg_field powerdown_to_x32;
	rand uvm_reg_field selfref_to_x32;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   powerdown_to_x32: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
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
	   selfref_to_x32: coverpoint {m_data[25:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_PWRTMG");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.powerdown_to_x32 = uvm_reg_field::type_id::create("powerdown_to_x32",,get_full_name());
      this.powerdown_to_x32.configure(this, 7, 0, "RW", 1, 7'h10, 1, 0, 1);
      this.selfref_to_x32 = uvm_reg_field::type_id::create("selfref_to_x32",,get_full_name());
      this.selfref_to_x32.configure(this, 10, 16, "RW", 1, 10'h40, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_PWRTMG)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_PWRTMG


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DDR4PPRTMG0 extends uvm_reg;
	rand uvm_reg_field t_pgm_x1_x1024;
	rand uvm_reg_field t_pgm_x1_sel;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   t_pgm_x1_x1024: coverpoint {m_data[21:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {23'b?????????????????????00};
	      wildcard bins bit_0_wr_as_1 = {23'b?????????????????????10};
	      wildcard bins bit_0_rd_as_0 = {23'b?????????????????????01};
	      wildcard bins bit_0_rd_as_1 = {23'b?????????????????????11};
	      wildcard bins bit_1_wr_as_0 = {23'b????????????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {23'b????????????????????1?0};
	      wildcard bins bit_1_rd_as_0 = {23'b????????????????????0?1};
	      wildcard bins bit_1_rd_as_1 = {23'b????????????????????1?1};
	      wildcard bins bit_2_wr_as_0 = {23'b???????????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {23'b???????????????????1??0};
	      wildcard bins bit_2_rd_as_0 = {23'b???????????????????0??1};
	      wildcard bins bit_2_rd_as_1 = {23'b???????????????????1??1};
	      wildcard bins bit_3_wr_as_0 = {23'b??????????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {23'b??????????????????1???0};
	      wildcard bins bit_3_rd_as_0 = {23'b??????????????????0???1};
	      wildcard bins bit_3_rd_as_1 = {23'b??????????????????1???1};
	      wildcard bins bit_4_wr_as_0 = {23'b?????????????????0????0};
	      wildcard bins bit_4_wr_as_1 = {23'b?????????????????1????0};
	      wildcard bins bit_4_rd_as_0 = {23'b?????????????????0????1};
	      wildcard bins bit_4_rd_as_1 = {23'b?????????????????1????1};
	      wildcard bins bit_5_wr_as_0 = {23'b????????????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {23'b????????????????1?????0};
	      wildcard bins bit_5_rd_as_0 = {23'b????????????????0?????1};
	      wildcard bins bit_5_rd_as_1 = {23'b????????????????1?????1};
	      wildcard bins bit_6_wr_as_0 = {23'b???????????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {23'b???????????????1??????0};
	      wildcard bins bit_6_rd_as_0 = {23'b???????????????0??????1};
	      wildcard bins bit_6_rd_as_1 = {23'b???????????????1??????1};
	      wildcard bins bit_7_wr_as_0 = {23'b??????????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {23'b??????????????1???????0};
	      wildcard bins bit_7_rd_as_0 = {23'b??????????????0???????1};
	      wildcard bins bit_7_rd_as_1 = {23'b??????????????1???????1};
	      wildcard bins bit_8_wr_as_0 = {23'b?????????????0????????0};
	      wildcard bins bit_8_wr_as_1 = {23'b?????????????1????????0};
	      wildcard bins bit_8_rd_as_0 = {23'b?????????????0????????1};
	      wildcard bins bit_8_rd_as_1 = {23'b?????????????1????????1};
	      wildcard bins bit_9_wr_as_0 = {23'b????????????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {23'b????????????1?????????0};
	      wildcard bins bit_9_rd_as_0 = {23'b????????????0?????????1};
	      wildcard bins bit_9_rd_as_1 = {23'b????????????1?????????1};
	      wildcard bins bit_10_wr_as_0 = {23'b???????????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {23'b???????????1??????????0};
	      wildcard bins bit_10_rd_as_0 = {23'b???????????0??????????1};
	      wildcard bins bit_10_rd_as_1 = {23'b???????????1??????????1};
	      wildcard bins bit_11_wr_as_0 = {23'b??????????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {23'b??????????1???????????0};
	      wildcard bins bit_11_rd_as_0 = {23'b??????????0???????????1};
	      wildcard bins bit_11_rd_as_1 = {23'b??????????1???????????1};
	      wildcard bins bit_12_wr_as_0 = {23'b?????????0????????????0};
	      wildcard bins bit_12_wr_as_1 = {23'b?????????1????????????0};
	      wildcard bins bit_12_rd_as_0 = {23'b?????????0????????????1};
	      wildcard bins bit_12_rd_as_1 = {23'b?????????1????????????1};
	      wildcard bins bit_13_wr_as_0 = {23'b????????0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {23'b????????1?????????????0};
	      wildcard bins bit_13_rd_as_0 = {23'b????????0?????????????1};
	      wildcard bins bit_13_rd_as_1 = {23'b????????1?????????????1};
	      wildcard bins bit_14_wr_as_0 = {23'b???????0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {23'b???????1??????????????0};
	      wildcard bins bit_14_rd_as_0 = {23'b???????0??????????????1};
	      wildcard bins bit_14_rd_as_1 = {23'b???????1??????????????1};
	      wildcard bins bit_15_wr_as_0 = {23'b??????0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {23'b??????1???????????????0};
	      wildcard bins bit_15_rd_as_0 = {23'b??????0???????????????1};
	      wildcard bins bit_15_rd_as_1 = {23'b??????1???????????????1};
	      wildcard bins bit_16_wr_as_0 = {23'b?????0????????????????0};
	      wildcard bins bit_16_wr_as_1 = {23'b?????1????????????????0};
	      wildcard bins bit_16_rd_as_0 = {23'b?????0????????????????1};
	      wildcard bins bit_16_rd_as_1 = {23'b?????1????????????????1};
	      wildcard bins bit_17_wr_as_0 = {23'b????0?????????????????0};
	      wildcard bins bit_17_wr_as_1 = {23'b????1?????????????????0};
	      wildcard bins bit_17_rd_as_0 = {23'b????0?????????????????1};
	      wildcard bins bit_17_rd_as_1 = {23'b????1?????????????????1};
	      wildcard bins bit_18_wr_as_0 = {23'b???0??????????????????0};
	      wildcard bins bit_18_wr_as_1 = {23'b???1??????????????????0};
	      wildcard bins bit_18_rd_as_0 = {23'b???0??????????????????1};
	      wildcard bins bit_18_rd_as_1 = {23'b???1??????????????????1};
	      wildcard bins bit_19_wr_as_0 = {23'b??0???????????????????0};
	      wildcard bins bit_19_wr_as_1 = {23'b??1???????????????????0};
	      wildcard bins bit_19_rd_as_0 = {23'b??0???????????????????1};
	      wildcard bins bit_19_rd_as_1 = {23'b??1???????????????????1};
	      wildcard bins bit_20_wr_as_0 = {23'b?0????????????????????0};
	      wildcard bins bit_20_wr_as_1 = {23'b?1????????????????????0};
	      wildcard bins bit_20_rd_as_0 = {23'b?0????????????????????1};
	      wildcard bins bit_20_rd_as_1 = {23'b?1????????????????????1};
	      wildcard bins bit_21_wr_as_0 = {23'b0?????????????????????0};
	      wildcard bins bit_21_wr_as_1 = {23'b1?????????????????????0};
	      wildcard bins bit_21_rd_as_0 = {23'b0?????????????????????1};
	      wildcard bins bit_21_rd_as_1 = {23'b1?????????????????????1};
	      option.weight = 88;
	   }
	   t_pgm_x1_sel: coverpoint {m_data[31:31], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DDR4PPRTMG0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.t_pgm_x1_x1024 = uvm_reg_field::type_id::create("t_pgm_x1_x1024",,get_full_name());
      this.t_pgm_x1_x1024.configure(this, 22, 0, "RW", 1, 22'h2faf09, 1, 0, 1);
      this.t_pgm_x1_sel = uvm_reg_field::type_id::create("t_pgm_x1_sel",,get_full_name());
      this.t_pgm_x1_sel.configure(this, 1, 31, "RW", 1, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DDR4PPRTMG0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DDR4PPRTMG0


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DDR4PPRTMG1 extends uvm_reg;
	rand uvm_reg_field t_pgmpst_x32;
	rand uvm_reg_field t_pgm_exit;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   t_pgmpst_x32: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	   t_pgm_exit: coverpoint {m_data[29:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_DDR4PPRTMG1");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.t_pgmpst_x32 = uvm_reg_field::type_id::create("t_pgmpst_x32",,get_full_name());
      this.t_pgmpst_x32.configure(this, 16, 0, "RW", 1, 16'h9c5, 1, 0, 1);
      this.t_pgm_exit = uvm_reg_field::type_id::create("t_pgm_exit",,get_full_name());
      this.t_pgm_exit.configure(this, 6, 24, "RW", 1, 6'h18, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DDR4PPRTMG1)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DDR4PPRTMG1


class ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_LNKECCCTL0 extends uvm_reg;
	rand uvm_reg_field wr_link_ecc_enable;
	rand uvm_reg_field rd_link_ecc_enable;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   wr_link_ecc_enable: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   rd_link_ecc_enable: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0_LNKECCCTL0");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.wr_link_ecc_enable = uvm_reg_field::type_id::create("wr_link_ecc_enable",,get_full_name());
      this.wr_link_ecc_enable.configure(this, 1, 0, "RW", 1, 1'h0, 1, 0, 0);
      this.rd_link_ecc_enable = uvm_reg_field::type_id::create("rd_link_ecc_enable",,get_full_name());
      this.rd_link_ecc_enable.configure(this, 1, 1, "RW", 1, 1'h0, 1, 0, 0);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_LNKECCCTL0)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_REG_BITS)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_LNKECCCTL0


class ral_block_DWC_ddrctl_map_REGB_FREQ0_CH0 extends uvm_reg_block;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG0 DRAMSET1TMG0;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG1 DRAMSET1TMG1;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG2 DRAMSET1TMG2;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG3 DRAMSET1TMG3;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG4 DRAMSET1TMG4;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG5 DRAMSET1TMG5;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG6 DRAMSET1TMG6;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG7 DRAMSET1TMG7;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG9 DRAMSET1TMG9;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG12 DRAMSET1TMG12;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG13 DRAMSET1TMG13;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG14 DRAMSET1TMG14;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG17 DRAMSET1TMG17;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG23 DRAMSET1TMG23;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG24 DRAMSET1TMG24;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG25 DRAMSET1TMG25;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG30 DRAMSET1TMG30;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG32 DRAMSET1TMG32;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR0 INITMR0;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR1 INITMR1;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR2 INITMR2;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR3 INITMR3;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG0 DFITMG0;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG1 DFITMG1;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG2 DFITMG2;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG4 DFITMG4;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG5 DFITMG5;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG6 DFITMG6;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFILPTMG0 DFILPTMG0;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFILPTMG1 DFILPTMG1;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG0 DFIUPDTMG0;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG1 DFIUPDTMG1;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG2 DFIUPDTMG2;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG3 DFIUPDTMG3;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG0 RFSHSET1TMG0;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG1 RFSHSET1TMG1;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG2 RFSHSET1TMG2;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG3 RFSHSET1TMG3;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG4 RFSHSET1TMG4;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFMSET1TMG0 RFMSET1TMG0;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_ZQSET1TMG0 ZQSET1TMG0;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_ZQSET1TMG1 ZQSET1TMG1;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_ZQSET1TMG2 ZQSET1TMG2;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DQSOSCCTL0 DQSOSCCTL0;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DERATEINT DERATEINT;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DERATEVAL0 DERATEVAL0;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DERATEVAL1 DERATEVAL1;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_HWLPTMG0 HWLPTMG0;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DVFSCTL0 DVFSCTL0;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_SCHEDTMG0 SCHEDTMG0;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_PERFHPR1 PERFHPR1;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_PERFLPR1 PERFLPR1;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_PERFWR1 PERFWR1;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_TMGCFG TMGCFG;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RANKTMG0 RANKTMG0;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RANKTMG1 RANKTMG1;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_PWRTMG PWRTMG;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DDR4PPRTMG0 DDR4PPRTMG0;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DDR4PPRTMG1 DDR4PPRTMG1;
	rand ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_LNKECCCTL0 LNKECCCTL0;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field DRAMSET1TMG0_t_ras_min;
	rand uvm_reg_field t_ras_min;
	rand uvm_reg_field DRAMSET1TMG0_t_ras_max;
	rand uvm_reg_field t_ras_max;
	rand uvm_reg_field DRAMSET1TMG0_t_faw;
	rand uvm_reg_field t_faw;
	rand uvm_reg_field DRAMSET1TMG0_wr2pre;
	rand uvm_reg_field wr2pre;
	rand uvm_reg_field DRAMSET1TMG1_t_rc;
	rand uvm_reg_field t_rc;
	rand uvm_reg_field DRAMSET1TMG1_rd2pre;
	rand uvm_reg_field rd2pre;
	rand uvm_reg_field DRAMSET1TMG1_t_xp;
	rand uvm_reg_field t_xp;
	rand uvm_reg_field DRAMSET1TMG1_t_rcd_write;
	rand uvm_reg_field t_rcd_write;
	rand uvm_reg_field DRAMSET1TMG2_wr2rd;
	rand uvm_reg_field wr2rd;
	rand uvm_reg_field DRAMSET1TMG2_rd2wr;
	rand uvm_reg_field rd2wr;
	rand uvm_reg_field DRAMSET1TMG2_read_latency;
	rand uvm_reg_field read_latency;
	rand uvm_reg_field DRAMSET1TMG2_write_latency;
	rand uvm_reg_field write_latency;
	rand uvm_reg_field DRAMSET1TMG3_wr2mr;
	rand uvm_reg_field wr2mr;
	rand uvm_reg_field DRAMSET1TMG3_rd2mr;
	rand uvm_reg_field rd2mr;
	rand uvm_reg_field DRAMSET1TMG3_t_mr;
	rand uvm_reg_field t_mr;
	rand uvm_reg_field DRAMSET1TMG4_t_rp;
	rand uvm_reg_field t_rp;
	rand uvm_reg_field DRAMSET1TMG4_t_rrd;
	rand uvm_reg_field t_rrd;
	rand uvm_reg_field DRAMSET1TMG4_t_ccd;
	rand uvm_reg_field t_ccd;
	rand uvm_reg_field DRAMSET1TMG4_t_rcd;
	rand uvm_reg_field t_rcd;
	rand uvm_reg_field DRAMSET1TMG5_t_cke;
	rand uvm_reg_field t_cke;
	rand uvm_reg_field DRAMSET1TMG5_t_ckesr;
	rand uvm_reg_field t_ckesr;
	rand uvm_reg_field DRAMSET1TMG5_t_cksre;
	rand uvm_reg_field t_cksre;
	rand uvm_reg_field DRAMSET1TMG5_t_cksrx;
	rand uvm_reg_field t_cksrx;
	rand uvm_reg_field DRAMSET1TMG6_t_ckcsx;
	rand uvm_reg_field t_ckcsx;
	rand uvm_reg_field DRAMSET1TMG7_t_csh;
	rand uvm_reg_field t_csh;
	rand uvm_reg_field DRAMSET1TMG9_wr2rd_s;
	rand uvm_reg_field wr2rd_s;
	rand uvm_reg_field DRAMSET1TMG9_t_rrd_s;
	rand uvm_reg_field t_rrd_s;
	rand uvm_reg_field DRAMSET1TMG9_t_ccd_s;
	rand uvm_reg_field t_ccd_s;
	rand uvm_reg_field DRAMSET1TMG12_t_cmdcke;
	rand uvm_reg_field t_cmdcke;
	rand uvm_reg_field DRAMSET1TMG13_t_ppd;
	rand uvm_reg_field t_ppd;
	rand uvm_reg_field DRAMSET1TMG13_t_ccd_mw;
	rand uvm_reg_field t_ccd_mw;
	rand uvm_reg_field DRAMSET1TMG13_odtloff;
	rand uvm_reg_field odtloff;
	rand uvm_reg_field DRAMSET1TMG14_t_xsr;
	rand uvm_reg_field t_xsr;
	rand uvm_reg_field DRAMSET1TMG14_t_osco;
	rand uvm_reg_field t_osco;
	rand uvm_reg_field DRAMSET1TMG17_t_vrcg_disable;
	rand uvm_reg_field t_vrcg_disable;
	rand uvm_reg_field DRAMSET1TMG17_t_vrcg_enable;
	rand uvm_reg_field t_vrcg_enable;
	rand uvm_reg_field DRAMSET1TMG23_t_pdn;
	rand uvm_reg_field t_pdn;
	rand uvm_reg_field DRAMSET1TMG23_t_xsr_dsm_x1024;
	rand uvm_reg_field t_xsr_dsm_x1024;
	rand uvm_reg_field DRAMSET1TMG24_max_wr_sync;
	rand uvm_reg_field max_wr_sync;
	rand uvm_reg_field DRAMSET1TMG24_max_rd_sync;
	rand uvm_reg_field max_rd_sync;
	rand uvm_reg_field DRAMSET1TMG24_rd2wr_s;
	rand uvm_reg_field rd2wr_s;
	rand uvm_reg_field DRAMSET1TMG24_bank_org;
	rand uvm_reg_field bank_org;
	rand uvm_reg_field DRAMSET1TMG25_rda2pre;
	rand uvm_reg_field rda2pre;
	rand uvm_reg_field DRAMSET1TMG25_wra2pre;
	rand uvm_reg_field wra2pre;
	rand uvm_reg_field DRAMSET1TMG25_lpddr4_diff_bank_rwa2pre;
	rand uvm_reg_field lpddr4_diff_bank_rwa2pre;
	rand uvm_reg_field DRAMSET1TMG30_mrr2rd;
	rand uvm_reg_field mrr2rd;
	rand uvm_reg_field DRAMSET1TMG30_mrr2wr;
	rand uvm_reg_field mrr2wr;
	rand uvm_reg_field DRAMSET1TMG30_mrr2mrw;
	rand uvm_reg_field mrr2mrw;
	rand uvm_reg_field DRAMSET1TMG32_ws_fs2wck_sus;
	rand uvm_reg_field ws_fs2wck_sus;
	rand uvm_reg_field DRAMSET1TMG32_t_wcksus;
	rand uvm_reg_field t_wcksus;
	rand uvm_reg_field DRAMSET1TMG32_ws_off2ws_fs;
	rand uvm_reg_field ws_off2ws_fs;
	rand uvm_reg_field INITMR0_emr;
	rand uvm_reg_field emr;
	rand uvm_reg_field INITMR0_mr;
	rand uvm_reg_field mr;
	rand uvm_reg_field INITMR1_emr3;
	rand uvm_reg_field emr3;
	rand uvm_reg_field INITMR1_emr2;
	rand uvm_reg_field emr2;
	rand uvm_reg_field INITMR2_mr5;
	rand uvm_reg_field mr5;
	rand uvm_reg_field INITMR2_mr4;
	rand uvm_reg_field mr4;
	rand uvm_reg_field INITMR3_mr6;
	rand uvm_reg_field mr6;
	rand uvm_reg_field INITMR3_mr22;
	rand uvm_reg_field mr22;
	rand uvm_reg_field DFITMG0_dfi_tphy_wrlat;
	rand uvm_reg_field dfi_tphy_wrlat;
	rand uvm_reg_field DFITMG0_dfi_tphy_wrdata;
	rand uvm_reg_field dfi_tphy_wrdata;
	rand uvm_reg_field DFITMG0_dfi_t_rddata_en;
	rand uvm_reg_field dfi_t_rddata_en;
	rand uvm_reg_field DFITMG0_dfi_t_ctrl_delay;
	rand uvm_reg_field dfi_t_ctrl_delay;
	rand uvm_reg_field DFITMG1_dfi_t_dram_clk_enable;
	rand uvm_reg_field dfi_t_dram_clk_enable;
	rand uvm_reg_field DFITMG1_dfi_t_dram_clk_disable;
	rand uvm_reg_field dfi_t_dram_clk_disable;
	rand uvm_reg_field DFITMG1_dfi_t_wrdata_delay;
	rand uvm_reg_field dfi_t_wrdata_delay;
	rand uvm_reg_field DFITMG2_dfi_tphy_wrcslat;
	rand uvm_reg_field dfi_tphy_wrcslat;
	rand uvm_reg_field DFITMG2_dfi_tphy_rdcslat;
	rand uvm_reg_field dfi_tphy_rdcslat;
	rand uvm_reg_field DFITMG2_dfi_twck_delay;
	rand uvm_reg_field dfi_twck_delay;
	rand uvm_reg_field DFITMG4_dfi_twck_dis;
	rand uvm_reg_field dfi_twck_dis;
	rand uvm_reg_field DFITMG4_dfi_twck_en_fs;
	rand uvm_reg_field dfi_twck_en_fs;
	rand uvm_reg_field DFITMG4_dfi_twck_en_wr;
	rand uvm_reg_field dfi_twck_en_wr;
	rand uvm_reg_field DFITMG4_dfi_twck_en_rd;
	rand uvm_reg_field dfi_twck_en_rd;
	rand uvm_reg_field DFITMG5_dfi_twck_toggle_post;
	rand uvm_reg_field dfi_twck_toggle_post;
	rand uvm_reg_field DFITMG5_dfi_twck_toggle_cs;
	rand uvm_reg_field dfi_twck_toggle_cs;
	rand uvm_reg_field DFITMG5_dfi_twck_toggle;
	rand uvm_reg_field dfi_twck_toggle;
	rand uvm_reg_field DFITMG5_dfi_twck_fast_toggle;
	rand uvm_reg_field dfi_twck_fast_toggle;
	rand uvm_reg_field DFITMG6_dfi_twck_toggle_post_rd;
	rand uvm_reg_field dfi_twck_toggle_post_rd;
	rand uvm_reg_field DFITMG6_dfi_twck_toggle_post_rd_en;
	rand uvm_reg_field dfi_twck_toggle_post_rd_en;
	rand uvm_reg_field DFILPTMG0_dfi_lp_wakeup_pd;
	rand uvm_reg_field dfi_lp_wakeup_pd;
	rand uvm_reg_field DFILPTMG0_dfi_lp_wakeup_sr;
	rand uvm_reg_field dfi_lp_wakeup_sr;
	rand uvm_reg_field DFILPTMG0_dfi_lp_wakeup_dsm;
	rand uvm_reg_field dfi_lp_wakeup_dsm;
	rand uvm_reg_field DFILPTMG1_dfi_lp_wakeup_data;
	rand uvm_reg_field dfi_lp_wakeup_data;
	rand uvm_reg_field DFILPTMG1_dfi_tlp_resp;
	rand uvm_reg_field dfi_tlp_resp;
	rand uvm_reg_field DFIUPDTMG0_dfi_t_ctrlup_min;
	rand uvm_reg_field dfi_t_ctrlup_min;
	rand uvm_reg_field DFIUPDTMG0_dfi_t_ctrlup_max;
	rand uvm_reg_field dfi_t_ctrlup_max;
	rand uvm_reg_field DFIUPDTMG1_dfi_t_ctrlupd_interval_max_x1024;
	rand uvm_reg_field dfi_t_ctrlupd_interval_max_x1024;
	rand uvm_reg_field DFIUPDTMG1_dfi_t_ctrlupd_interval_min_x1024;
	rand uvm_reg_field dfi_t_ctrlupd_interval_min_x1024;
	rand uvm_reg_field DFIUPDTMG2_dfi_t_ctrlupd_interval_type1;
	rand uvm_reg_field dfi_t_ctrlupd_interval_type1;
	rand uvm_reg_field DFIUPDTMG2_ctrlupd_after_dqsosc;
	rand uvm_reg_field ctrlupd_after_dqsosc;
	rand uvm_reg_field DFIUPDTMG2_ppt2_override;
	rand uvm_reg_field ppt2_override;
	rand uvm_reg_field DFIUPDTMG2_ppt2_en;
	rand uvm_reg_field ppt2_en;
	rand uvm_reg_field DFIUPDTMG2_dfi_t_ctrlupd_interval_type1_unit;
	rand uvm_reg_field dfi_t_ctrlupd_interval_type1_unit;
	rand uvm_reg_field DFIUPDTMG3_dfi_t_ctrlupd_burst_interval_x8;
	rand uvm_reg_field dfi_t_ctrlupd_burst_interval_x8;
	rand uvm_reg_field RFSHSET1TMG0_t_refi_x1_x32;
	rand uvm_reg_field t_refi_x1_x32;
	rand uvm_reg_field RFSHSET1TMG0_refresh_to_x1_x32;
	rand uvm_reg_field refresh_to_x1_x32;
	rand uvm_reg_field RFSHSET1TMG0_refresh_margin;
	rand uvm_reg_field refresh_margin;
	rand uvm_reg_field RFSHSET1TMG0_refresh_to_x1_sel;
	rand uvm_reg_field refresh_to_x1_sel;
	rand uvm_reg_field RFSHSET1TMG0_t_refi_x1_sel;
	rand uvm_reg_field t_refi_x1_sel;
	rand uvm_reg_field RFSHSET1TMG1_t_rfc_min;
	rand uvm_reg_field t_rfc_min;
	rand uvm_reg_field RFSHSET1TMG1_t_rfc_min_ab;
	rand uvm_reg_field t_rfc_min_ab;
	rand uvm_reg_field RFSHSET1TMG2_t_pbr2pbr;
	rand uvm_reg_field t_pbr2pbr;
	rand uvm_reg_field RFSHSET1TMG2_t_pbr2act;
	rand uvm_reg_field t_pbr2act;
	rand uvm_reg_field RFSHSET1TMG3_refresh_to_ab_x32;
	rand uvm_reg_field refresh_to_ab_x32;
	rand uvm_reg_field RFSHSET1TMG4_refresh_timer0_start_value_x32;
	rand uvm_reg_field refresh_timer0_start_value_x32;
	rand uvm_reg_field RFSHSET1TMG4_refresh_timer1_start_value_x32;
	rand uvm_reg_field refresh_timer1_start_value_x32;
	rand uvm_reg_field RFMSET1TMG0_t_rfmpb;
	rand uvm_reg_field t_rfmpb;
	rand uvm_reg_field ZQSET1TMG0_t_zq_long_nop;
	rand uvm_reg_field t_zq_long_nop;
	rand uvm_reg_field ZQSET1TMG0_t_zq_short_nop;
	rand uvm_reg_field t_zq_short_nop;
	rand uvm_reg_field ZQSET1TMG1_t_zq_short_interval_x1024;
	rand uvm_reg_field t_zq_short_interval_x1024;
	rand uvm_reg_field ZQSET1TMG1_t_zq_reset_nop;
	rand uvm_reg_field t_zq_reset_nop;
	rand uvm_reg_field ZQSET1TMG2_t_zq_stop;
	rand uvm_reg_field t_zq_stop;
	rand uvm_reg_field DQSOSCCTL0_dqsosc_enable;
	rand uvm_reg_field dqsosc_enable;
	rand uvm_reg_field DQSOSCCTL0_dqsosc_interval_unit;
	rand uvm_reg_field dqsosc_interval_unit;
	rand uvm_reg_field DQSOSCCTL0_dqsosc_interval;
	rand uvm_reg_field dqsosc_interval;
	rand uvm_reg_field DERATEINT_mr4_read_interval;
	rand uvm_reg_field mr4_read_interval;
	rand uvm_reg_field DERATEVAL0_derated_t_rrd;
	rand uvm_reg_field derated_t_rrd;
	rand uvm_reg_field DERATEVAL0_derated_t_rp;
	rand uvm_reg_field derated_t_rp;
	rand uvm_reg_field DERATEVAL0_derated_t_ras_min;
	rand uvm_reg_field derated_t_ras_min;
	rand uvm_reg_field DERATEVAL0_derated_t_rcd;
	rand uvm_reg_field derated_t_rcd;
	rand uvm_reg_field DERATEVAL1_derated_t_rc;
	rand uvm_reg_field derated_t_rc;
	rand uvm_reg_field DERATEVAL1_derated_t_rcd_write;
	rand uvm_reg_field derated_t_rcd_write;
	rand uvm_reg_field HWLPTMG0_hw_lp_idle_x32;
	rand uvm_reg_field hw_lp_idle_x32;
	rand uvm_reg_field DVFSCTL0_dvfsq_enable;
	rand uvm_reg_field dvfsq_enable;
	rand uvm_reg_field SCHEDTMG0_pageclose_timer;
	rand uvm_reg_field pageclose_timer;
	rand uvm_reg_field SCHEDTMG0_rdwr_idle_gap;
	rand uvm_reg_field rdwr_idle_gap;
	rand uvm_reg_field PERFHPR1_hpr_max_starve;
	rand uvm_reg_field hpr_max_starve;
	rand uvm_reg_field PERFHPR1_hpr_xact_run_length;
	rand uvm_reg_field hpr_xact_run_length;
	rand uvm_reg_field PERFLPR1_lpr_max_starve;
	rand uvm_reg_field lpr_max_starve;
	rand uvm_reg_field PERFLPR1_lpr_xact_run_length;
	rand uvm_reg_field lpr_xact_run_length;
	rand uvm_reg_field PERFWR1_w_max_starve;
	rand uvm_reg_field w_max_starve;
	rand uvm_reg_field PERFWR1_w_xact_run_length;
	rand uvm_reg_field w_xact_run_length;
	rand uvm_reg_field TMGCFG_frequency_ratio;
	rand uvm_reg_field frequency_ratio;
	rand uvm_reg_field RANKTMG0_diff_rank_rd_gap;
	rand uvm_reg_field diff_rank_rd_gap;
	rand uvm_reg_field RANKTMG0_diff_rank_wr_gap;
	rand uvm_reg_field diff_rank_wr_gap;
	rand uvm_reg_field RANKTMG1_wr2rd_dr;
	rand uvm_reg_field wr2rd_dr;
	rand uvm_reg_field RANKTMG1_rd2wr_dr;
	rand uvm_reg_field rd2wr_dr;
	rand uvm_reg_field PWRTMG_powerdown_to_x32;
	rand uvm_reg_field powerdown_to_x32;
	rand uvm_reg_field PWRTMG_selfref_to_x32;
	rand uvm_reg_field selfref_to_x32;
	rand uvm_reg_field DDR4PPRTMG0_t_pgm_x1_x1024;
	rand uvm_reg_field t_pgm_x1_x1024;
	rand uvm_reg_field DDR4PPRTMG0_t_pgm_x1_sel;
	rand uvm_reg_field t_pgm_x1_sel;
	rand uvm_reg_field DDR4PPRTMG1_t_pgmpst_x32;
	rand uvm_reg_field t_pgmpst_x32;
	rand uvm_reg_field DDR4PPRTMG1_t_pgm_exit;
	rand uvm_reg_field t_pgm_exit;
	rand uvm_reg_field LNKECCCTL0_wr_link_ecc_enable;
	rand uvm_reg_field wr_link_ecc_enable;
	rand uvm_reg_field LNKECCCTL0_rd_link_ecc_enable;
	rand uvm_reg_field rd_link_ecc_enable;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	DRAMSET1TMG0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h0 };
		option.weight = 1;
	}

	DRAMSET1TMG1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4 };
		option.weight = 1;
	}

	DRAMSET1TMG2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h8 };
		option.weight = 1;
	}

	DRAMSET1TMG3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC };
		option.weight = 1;
	}

	DRAMSET1TMG4 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h10 };
		option.weight = 1;
	}

	DRAMSET1TMG5 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h14 };
		option.weight = 1;
	}

	DRAMSET1TMG6 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h18 };
		option.weight = 1;
	}

	DRAMSET1TMG7 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h1C };
		option.weight = 1;
	}

	DRAMSET1TMG9 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h24 };
		option.weight = 1;
	}

	DRAMSET1TMG12 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h30 };
		option.weight = 1;
	}

	DRAMSET1TMG13 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h34 };
		option.weight = 1;
	}

	DRAMSET1TMG14 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h38 };
		option.weight = 1;
	}

	DRAMSET1TMG17 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h44 };
		option.weight = 1;
	}

	DRAMSET1TMG23 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5C };
		option.weight = 1;
	}

	DRAMSET1TMG24 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h60 };
		option.weight = 1;
	}

	DRAMSET1TMG25 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h64 };
		option.weight = 1;
	}

	DRAMSET1TMG30 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h78 };
		option.weight = 1;
	}

	DRAMSET1TMG32 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h80 };
		option.weight = 1;
	}

	INITMR0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h500 };
		option.weight = 1;
	}

	INITMR1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h504 };
		option.weight = 1;
	}

	INITMR2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h508 };
		option.weight = 1;
	}

	INITMR3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h50C };
		option.weight = 1;
	}

	DFITMG0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h580 };
		option.weight = 1;
	}

	DFITMG1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h584 };
		option.weight = 1;
	}

	DFITMG2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h588 };
		option.weight = 1;
	}

	DFITMG4 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h590 };
		option.weight = 1;
	}

	DFITMG5 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h594 };
		option.weight = 1;
	}

	DFITMG6 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h598 };
		option.weight = 1;
	}

	DFILPTMG0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5A0 };
		option.weight = 1;
	}

	DFILPTMG1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5A4 };
		option.weight = 1;
	}

	DFIUPDTMG0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5A8 };
		option.weight = 1;
	}

	DFIUPDTMG1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5AC };
		option.weight = 1;
	}

	DFIUPDTMG2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5B4 };
		option.weight = 1;
	}

	DFIUPDTMG3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h5B8 };
		option.weight = 1;
	}

	RFSHSET1TMG0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h600 };
		option.weight = 1;
	}

	RFSHSET1TMG1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h604 };
		option.weight = 1;
	}

	RFSHSET1TMG2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h608 };
		option.weight = 1;
	}

	RFSHSET1TMG3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h60C };
		option.weight = 1;
	}

	RFSHSET1TMG4 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h610 };
		option.weight = 1;
	}

	RFMSET1TMG0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h650 };
		option.weight = 1;
	}

	ZQSET1TMG0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h800 };
		option.weight = 1;
	}

	ZQSET1TMG1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h804 };
		option.weight = 1;
	}

	ZQSET1TMG2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h808 };
		option.weight = 1;
	}

	DQSOSCCTL0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hA80 };
		option.weight = 1;
	}

	DERATEINT : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB00 };
		option.weight = 1;
	}

	DERATEVAL0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB04 };
		option.weight = 1;
	}

	DERATEVAL1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB08 };
		option.weight = 1;
	}

	HWLPTMG0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB80 };
		option.weight = 1;
	}

	DVFSCTL0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB84 };
		option.weight = 1;
	}

	SCHEDTMG0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC00 };
		option.weight = 1;
	}

	PERFHPR1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC80 };
		option.weight = 1;
	}

	PERFLPR1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC84 };
		option.weight = 1;
	}

	PERFWR1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC88 };
		option.weight = 1;
	}

	TMGCFG : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD00 };
		option.weight = 1;
	}

	RANKTMG0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD04 };
		option.weight = 1;
	}

	RANKTMG1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD08 };
		option.weight = 1;
	}

	PWRTMG : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD0C };
		option.weight = 1;
	}

	DDR4PPRTMG0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD30 };
		option.weight = 1;
	}

	DDR4PPRTMG1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD34 };
		option.weight = 1;
	}

	LNKECCCTL0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD80 };
		option.weight = 1;
	}
endgroup
	function new(string name = "DWC_ddrctl_map_REGB_FREQ0_CH0");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.DRAMSET1TMG0 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG0::type_id::create("DRAMSET1TMG0",,get_full_name());
      if(this.DRAMSET1TMG0.has_coverage(UVM_CVR_REG_BITS))
      	this.DRAMSET1TMG0.cg_bits.option.name = {get_name(), ".", "DRAMSET1TMG0_bits"};
      this.DRAMSET1TMG0.configure(this, null, "");
      this.DRAMSET1TMG0.build();
	  uvm_resource_db#(string)::set({"REG::", DRAMSET1TMG0.get_full_name()}, "accessType", "NONSECURE", this);
         this.DRAMSET1TMG0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_ras_min", 0, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_ras_max", 8, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_faw", 16, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_wr2pre", 24, 8}
         });
      this.default_map.add_reg(this.DRAMSET1TMG0, `UVM_REG_ADDR_WIDTH'h0, "RW", 0);
		this.DRAMSET1TMG0_t_ras_min = this.DRAMSET1TMG0.t_ras_min;
		this.t_ras_min = this.DRAMSET1TMG0.t_ras_min;
		this.DRAMSET1TMG0_t_ras_max = this.DRAMSET1TMG0.t_ras_max;
		this.t_ras_max = this.DRAMSET1TMG0.t_ras_max;
		this.DRAMSET1TMG0_t_faw = this.DRAMSET1TMG0.t_faw;
		this.t_faw = this.DRAMSET1TMG0.t_faw;
		this.DRAMSET1TMG0_wr2pre = this.DRAMSET1TMG0.wr2pre;
		this.wr2pre = this.DRAMSET1TMG0.wr2pre;
      this.DRAMSET1TMG1 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG1::type_id::create("DRAMSET1TMG1",,get_full_name());
      if(this.DRAMSET1TMG1.has_coverage(UVM_CVR_REG_BITS))
      	this.DRAMSET1TMG1.cg_bits.option.name = {get_name(), ".", "DRAMSET1TMG1_bits"};
      this.DRAMSET1TMG1.configure(this, null, "");
      this.DRAMSET1TMG1.build();
	  uvm_resource_db#(string)::set({"REG::", DRAMSET1TMG1.get_full_name()}, "accessType", "NONSECURE", this);
         this.DRAMSET1TMG1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_rc", 0, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_rd2pre", 8, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_xp", 16, 6},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_rcd_write", 24, 8}
         });
      this.default_map.add_reg(this.DRAMSET1TMG1, `UVM_REG_ADDR_WIDTH'h4, "RW", 0);
		this.DRAMSET1TMG1_t_rc = this.DRAMSET1TMG1.t_rc;
		this.t_rc = this.DRAMSET1TMG1.t_rc;
		this.DRAMSET1TMG1_rd2pre = this.DRAMSET1TMG1.rd2pre;
		this.rd2pre = this.DRAMSET1TMG1.rd2pre;
		this.DRAMSET1TMG1_t_xp = this.DRAMSET1TMG1.t_xp;
		this.t_xp = this.DRAMSET1TMG1.t_xp;
		this.DRAMSET1TMG1_t_rcd_write = this.DRAMSET1TMG1.t_rcd_write;
		this.t_rcd_write = this.DRAMSET1TMG1.t_rcd_write;
      this.DRAMSET1TMG2 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG2::type_id::create("DRAMSET1TMG2",,get_full_name());
      if(this.DRAMSET1TMG2.has_coverage(UVM_CVR_REG_BITS))
      	this.DRAMSET1TMG2.cg_bits.option.name = {get_name(), ".", "DRAMSET1TMG2_bits"};
      this.DRAMSET1TMG2.configure(this, null, "");
      this.DRAMSET1TMG2.build();
	  uvm_resource_db#(string)::set({"REG::", DRAMSET1TMG2.get_full_name()}, "accessType", "NONSECURE", this);
         this.DRAMSET1TMG2.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_wr2rd", 0, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_rd2wr", 8, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_read_latency", 16, 7},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_write_latency", 24, 7}
         });
      this.default_map.add_reg(this.DRAMSET1TMG2, `UVM_REG_ADDR_WIDTH'h8, "RW", 0);
		this.DRAMSET1TMG2_wr2rd = this.DRAMSET1TMG2.wr2rd;
		this.wr2rd = this.DRAMSET1TMG2.wr2rd;
		this.DRAMSET1TMG2_rd2wr = this.DRAMSET1TMG2.rd2wr;
		this.rd2wr = this.DRAMSET1TMG2.rd2wr;
		this.DRAMSET1TMG2_read_latency = this.DRAMSET1TMG2.read_latency;
		this.read_latency = this.DRAMSET1TMG2.read_latency;
		this.DRAMSET1TMG2_write_latency = this.DRAMSET1TMG2.write_latency;
		this.write_latency = this.DRAMSET1TMG2.write_latency;
      this.DRAMSET1TMG3 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG3::type_id::create("DRAMSET1TMG3",,get_full_name());
      if(this.DRAMSET1TMG3.has_coverage(UVM_CVR_REG_BITS))
      	this.DRAMSET1TMG3.cg_bits.option.name = {get_name(), ".", "DRAMSET1TMG3_bits"};
      this.DRAMSET1TMG3.configure(this, null, "");
      this.DRAMSET1TMG3.build();
	  uvm_resource_db#(string)::set({"REG::", DRAMSET1TMG3.get_full_name()}, "accessType", "NONSECURE", this);
         this.DRAMSET1TMG3.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_wr2mr", 0, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_rd2mr", 8, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_mr", 16, 7}
         });
      this.default_map.add_reg(this.DRAMSET1TMG3, `UVM_REG_ADDR_WIDTH'hC, "RW", 0);
		this.DRAMSET1TMG3_wr2mr = this.DRAMSET1TMG3.wr2mr;
		this.wr2mr = this.DRAMSET1TMG3.wr2mr;
		this.DRAMSET1TMG3_rd2mr = this.DRAMSET1TMG3.rd2mr;
		this.rd2mr = this.DRAMSET1TMG3.rd2mr;
		this.DRAMSET1TMG3_t_mr = this.DRAMSET1TMG3.t_mr;
		this.t_mr = this.DRAMSET1TMG3.t_mr;
      this.DRAMSET1TMG4 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG4::type_id::create("DRAMSET1TMG4",,get_full_name());
      if(this.DRAMSET1TMG4.has_coverage(UVM_CVR_REG_BITS))
      	this.DRAMSET1TMG4.cg_bits.option.name = {get_name(), ".", "DRAMSET1TMG4_bits"};
      this.DRAMSET1TMG4.configure(this, null, "");
      this.DRAMSET1TMG4.build();
	  uvm_resource_db#(string)::set({"REG::", DRAMSET1TMG4.get_full_name()}, "accessType", "NONSECURE", this);
         this.DRAMSET1TMG4.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_rp", 0, 7},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_rrd", 8, 6},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_ccd", 16, 6},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_rcd", 24, 8}
         });
      this.default_map.add_reg(this.DRAMSET1TMG4, `UVM_REG_ADDR_WIDTH'h10, "RW", 0);
		this.DRAMSET1TMG4_t_rp = this.DRAMSET1TMG4.t_rp;
		this.t_rp = this.DRAMSET1TMG4.t_rp;
		this.DRAMSET1TMG4_t_rrd = this.DRAMSET1TMG4.t_rrd;
		this.t_rrd = this.DRAMSET1TMG4.t_rrd;
		this.DRAMSET1TMG4_t_ccd = this.DRAMSET1TMG4.t_ccd;
		this.t_ccd = this.DRAMSET1TMG4.t_ccd;
		this.DRAMSET1TMG4_t_rcd = this.DRAMSET1TMG4.t_rcd;
		this.t_rcd = this.DRAMSET1TMG4.t_rcd;
      this.DRAMSET1TMG5 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG5::type_id::create("DRAMSET1TMG5",,get_full_name());
      if(this.DRAMSET1TMG5.has_coverage(UVM_CVR_REG_BITS))
      	this.DRAMSET1TMG5.cg_bits.option.name = {get_name(), ".", "DRAMSET1TMG5_bits"};
      this.DRAMSET1TMG5.configure(this, null, "");
      this.DRAMSET1TMG5.build();
	  uvm_resource_db#(string)::set({"REG::", DRAMSET1TMG5.get_full_name()}, "accessType", "NONSECURE", this);
         this.DRAMSET1TMG5.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_t_cke", 0, 6},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_t_ckesr", 8, 7},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_t_cksre", 16, 7},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_t_cksrx", 24, 6}
         });
      this.default_map.add_reg(this.DRAMSET1TMG5, `UVM_REG_ADDR_WIDTH'h14, "RW", 0);
		this.DRAMSET1TMG5_t_cke = this.DRAMSET1TMG5.t_cke;
		this.t_cke = this.DRAMSET1TMG5.t_cke;
		this.DRAMSET1TMG5_t_ckesr = this.DRAMSET1TMG5.t_ckesr;
		this.t_ckesr = this.DRAMSET1TMG5.t_ckesr;
		this.DRAMSET1TMG5_t_cksre = this.DRAMSET1TMG5.t_cksre;
		this.t_cksre = this.DRAMSET1TMG5.t_cksre;
		this.DRAMSET1TMG5_t_cksrx = this.DRAMSET1TMG5.t_cksrx;
		this.t_cksrx = this.DRAMSET1TMG5.t_cksrx;
      this.DRAMSET1TMG6 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG6::type_id::create("DRAMSET1TMG6",,get_full_name());
      if(this.DRAMSET1TMG6.has_coverage(UVM_CVR_REG_BITS))
      	this.DRAMSET1TMG6.cg_bits.option.name = {get_name(), ".", "DRAMSET1TMG6_bits"};
      this.DRAMSET1TMG6.configure(this, null, "");
      this.DRAMSET1TMG6.build();
	  uvm_resource_db#(string)::set({"REG::", DRAMSET1TMG6.get_full_name()}, "accessType", "NONSECURE", this);
         this.DRAMSET1TMG6.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_ckcsx", 0, 6}
         });
      this.default_map.add_reg(this.DRAMSET1TMG6, `UVM_REG_ADDR_WIDTH'h18, "RW", 0);
		this.DRAMSET1TMG6_t_ckcsx = this.DRAMSET1TMG6.t_ckcsx;
		this.t_ckcsx = this.DRAMSET1TMG6.t_ckcsx;
      this.DRAMSET1TMG7 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG7::type_id::create("DRAMSET1TMG7",,get_full_name());
      if(this.DRAMSET1TMG7.has_coverage(UVM_CVR_REG_BITS))
      	this.DRAMSET1TMG7.cg_bits.option.name = {get_name(), ".", "DRAMSET1TMG7_bits"};
      this.DRAMSET1TMG7.configure(this, null, "");
      this.DRAMSET1TMG7.build();
	  uvm_resource_db#(string)::set({"REG::", DRAMSET1TMG7.get_full_name()}, "accessType", "NONSECURE", this);
         this.DRAMSET1TMG7.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_t_csh", 0, 4}
         });
      this.default_map.add_reg(this.DRAMSET1TMG7, `UVM_REG_ADDR_WIDTH'h1C, "RW", 0);
		this.DRAMSET1TMG7_t_csh = this.DRAMSET1TMG7.t_csh;
		this.t_csh = this.DRAMSET1TMG7.t_csh;
      this.DRAMSET1TMG9 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG9::type_id::create("DRAMSET1TMG9",,get_full_name());
      if(this.DRAMSET1TMG9.has_coverage(UVM_CVR_REG_BITS))
      	this.DRAMSET1TMG9.cg_bits.option.name = {get_name(), ".", "DRAMSET1TMG9_bits"};
      this.DRAMSET1TMG9.configure(this, null, "");
      this.DRAMSET1TMG9.build();
	  uvm_resource_db#(string)::set({"REG::", DRAMSET1TMG9.get_full_name()}, "accessType", "NONSECURE", this);
         this.DRAMSET1TMG9.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_wr2rd_s", 0, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_rrd_s", 8, 6},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_ccd_s", 16, 5}
         });
      this.default_map.add_reg(this.DRAMSET1TMG9, `UVM_REG_ADDR_WIDTH'h24, "RW", 0);
		this.DRAMSET1TMG9_wr2rd_s = this.DRAMSET1TMG9.wr2rd_s;
		this.wr2rd_s = this.DRAMSET1TMG9.wr2rd_s;
		this.DRAMSET1TMG9_t_rrd_s = this.DRAMSET1TMG9.t_rrd_s;
		this.t_rrd_s = this.DRAMSET1TMG9.t_rrd_s;
		this.DRAMSET1TMG9_t_ccd_s = this.DRAMSET1TMG9.t_ccd_s;
		this.t_ccd_s = this.DRAMSET1TMG9.t_ccd_s;
      this.DRAMSET1TMG12 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG12::type_id::create("DRAMSET1TMG12",,get_full_name());
      if(this.DRAMSET1TMG12.has_coverage(UVM_CVR_REG_BITS))
      	this.DRAMSET1TMG12.cg_bits.option.name = {get_name(), ".", "DRAMSET1TMG12_bits"};
      this.DRAMSET1TMG12.configure(this, null, "");
      this.DRAMSET1TMG12.build();
	  uvm_resource_db#(string)::set({"REG::", DRAMSET1TMG12.get_full_name()}, "accessType", "NONSECURE", this);
         this.DRAMSET1TMG12.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_cmdcke", 16, 4}
         });
      this.default_map.add_reg(this.DRAMSET1TMG12, `UVM_REG_ADDR_WIDTH'h30, "RW", 0);
		this.DRAMSET1TMG12_t_cmdcke = this.DRAMSET1TMG12.t_cmdcke;
		this.t_cmdcke = this.DRAMSET1TMG12.t_cmdcke;
      this.DRAMSET1TMG13 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG13::type_id::create("DRAMSET1TMG13",,get_full_name());
      if(this.DRAMSET1TMG13.has_coverage(UVM_CVR_REG_BITS))
      	this.DRAMSET1TMG13.cg_bits.option.name = {get_name(), ".", "DRAMSET1TMG13_bits"};
      this.DRAMSET1TMG13.configure(this, null, "");
      this.DRAMSET1TMG13.build();
	  uvm_resource_db#(string)::set({"REG::", DRAMSET1TMG13.get_full_name()}, "accessType", "NONSECURE", this);
         this.DRAMSET1TMG13.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_ppd", 0, 4},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_ccd_mw", 16, 7},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_odtloff", 24, 7}
         });
      this.default_map.add_reg(this.DRAMSET1TMG13, `UVM_REG_ADDR_WIDTH'h34, "RW", 0);
		this.DRAMSET1TMG13_t_ppd = this.DRAMSET1TMG13.t_ppd;
		this.t_ppd = this.DRAMSET1TMG13.t_ppd;
		this.DRAMSET1TMG13_t_ccd_mw = this.DRAMSET1TMG13.t_ccd_mw;
		this.t_ccd_mw = this.DRAMSET1TMG13.t_ccd_mw;
		this.DRAMSET1TMG13_odtloff = this.DRAMSET1TMG13.odtloff;
		this.odtloff = this.DRAMSET1TMG13.odtloff;
      this.DRAMSET1TMG14 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG14::type_id::create("DRAMSET1TMG14",,get_full_name());
      if(this.DRAMSET1TMG14.has_coverage(UVM_CVR_REG_BITS))
      	this.DRAMSET1TMG14.cg_bits.option.name = {get_name(), ".", "DRAMSET1TMG14_bits"};
      this.DRAMSET1TMG14.configure(this, null, "");
      this.DRAMSET1TMG14.build();
	  uvm_resource_db#(string)::set({"REG::", DRAMSET1TMG14.get_full_name()}, "accessType", "NONSECURE", this);
         this.DRAMSET1TMG14.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_xsr", 0, 12},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_osco", 16, 9}
         });
      this.default_map.add_reg(this.DRAMSET1TMG14, `UVM_REG_ADDR_WIDTH'h38, "RW", 0);
		this.DRAMSET1TMG14_t_xsr = this.DRAMSET1TMG14.t_xsr;
		this.t_xsr = this.DRAMSET1TMG14.t_xsr;
		this.DRAMSET1TMG14_t_osco = this.DRAMSET1TMG14.t_osco;
		this.t_osco = this.DRAMSET1TMG14.t_osco;
      this.DRAMSET1TMG17 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG17::type_id::create("DRAMSET1TMG17",,get_full_name());
      if(this.DRAMSET1TMG17.has_coverage(UVM_CVR_REG_BITS))
      	this.DRAMSET1TMG17.cg_bits.option.name = {get_name(), ".", "DRAMSET1TMG17_bits"};
      this.DRAMSET1TMG17.configure(this, null, "");
      this.DRAMSET1TMG17.build();
	  uvm_resource_db#(string)::set({"REG::", DRAMSET1TMG17.get_full_name()}, "accessType", "NONSECURE", this);
         this.DRAMSET1TMG17.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_vrcg_disable", 0, 10},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_vrcg_enable", 16, 10}
         });
      this.default_map.add_reg(this.DRAMSET1TMG17, `UVM_REG_ADDR_WIDTH'h44, "RW", 0);
		this.DRAMSET1TMG17_t_vrcg_disable = this.DRAMSET1TMG17.t_vrcg_disable;
		this.t_vrcg_disable = this.DRAMSET1TMG17.t_vrcg_disable;
		this.DRAMSET1TMG17_t_vrcg_enable = this.DRAMSET1TMG17.t_vrcg_enable;
		this.t_vrcg_enable = this.DRAMSET1TMG17.t_vrcg_enable;
      this.DRAMSET1TMG23 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG23::type_id::create("DRAMSET1TMG23",,get_full_name());
      if(this.DRAMSET1TMG23.has_coverage(UVM_CVR_REG_BITS))
      	this.DRAMSET1TMG23.cg_bits.option.name = {get_name(), ".", "DRAMSET1TMG23_bits"};
      this.DRAMSET1TMG23.configure(this, null, "");
      this.DRAMSET1TMG23.build();
	  uvm_resource_db#(string)::set({"REG::", DRAMSET1TMG23.get_full_name()}, "accessType", "NONSECURE", this);
         this.DRAMSET1TMG23.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_t_pdn", 0, 12},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_t_xsr_dsm_x1024", 16, 8}
         });
      this.default_map.add_reg(this.DRAMSET1TMG23, `UVM_REG_ADDR_WIDTH'h5C, "RW", 0);
		this.DRAMSET1TMG23_t_pdn = this.DRAMSET1TMG23.t_pdn;
		this.t_pdn = this.DRAMSET1TMG23.t_pdn;
		this.DRAMSET1TMG23_t_xsr_dsm_x1024 = this.DRAMSET1TMG23.t_xsr_dsm_x1024;
		this.t_xsr_dsm_x1024 = this.DRAMSET1TMG23.t_xsr_dsm_x1024;
      this.DRAMSET1TMG24 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG24::type_id::create("DRAMSET1TMG24",,get_full_name());
      if(this.DRAMSET1TMG24.has_coverage(UVM_CVR_REG_BITS))
      	this.DRAMSET1TMG24.cg_bits.option.name = {get_name(), ".", "DRAMSET1TMG24_bits"};
      this.DRAMSET1TMG24.configure(this, null, "");
      this.DRAMSET1TMG24.build();
	  uvm_resource_db#(string)::set({"REG::", DRAMSET1TMG24.get_full_name()}, "accessType", "NONSECURE", this);
         this.DRAMSET1TMG24.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_max_wr_sync", 0, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_max_rd_sync", 8, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_rd2wr_s", 16, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_bank_org", 24, 2}
         });
      this.default_map.add_reg(this.DRAMSET1TMG24, `UVM_REG_ADDR_WIDTH'h60, "RW", 0);
		this.DRAMSET1TMG24_max_wr_sync = this.DRAMSET1TMG24.max_wr_sync;
		this.max_wr_sync = this.DRAMSET1TMG24.max_wr_sync;
		this.DRAMSET1TMG24_max_rd_sync = this.DRAMSET1TMG24.max_rd_sync;
		this.max_rd_sync = this.DRAMSET1TMG24.max_rd_sync;
		this.DRAMSET1TMG24_rd2wr_s = this.DRAMSET1TMG24.rd2wr_s;
		this.rd2wr_s = this.DRAMSET1TMG24.rd2wr_s;
		this.DRAMSET1TMG24_bank_org = this.DRAMSET1TMG24.bank_org;
		this.bank_org = this.DRAMSET1TMG24.bank_org;
      this.DRAMSET1TMG25 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG25::type_id::create("DRAMSET1TMG25",,get_full_name());
      if(this.DRAMSET1TMG25.has_coverage(UVM_CVR_REG_BITS))
      	this.DRAMSET1TMG25.cg_bits.option.name = {get_name(), ".", "DRAMSET1TMG25_bits"};
      this.DRAMSET1TMG25.configure(this, null, "");
      this.DRAMSET1TMG25.build();
	  uvm_resource_db#(string)::set({"REG::", DRAMSET1TMG25.get_full_name()}, "accessType", "NONSECURE", this);
         this.DRAMSET1TMG25.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_rda2pre", 0, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_wra2pre", 8, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_lpddr4_diff_bank_rwa2pre", 16, 3}
         });
      this.default_map.add_reg(this.DRAMSET1TMG25, `UVM_REG_ADDR_WIDTH'h64, "RW", 0);
		this.DRAMSET1TMG25_rda2pre = this.DRAMSET1TMG25.rda2pre;
		this.rda2pre = this.DRAMSET1TMG25.rda2pre;
		this.DRAMSET1TMG25_wra2pre = this.DRAMSET1TMG25.wra2pre;
		this.wra2pre = this.DRAMSET1TMG25.wra2pre;
		this.DRAMSET1TMG25_lpddr4_diff_bank_rwa2pre = this.DRAMSET1TMG25.lpddr4_diff_bank_rwa2pre;
		this.lpddr4_diff_bank_rwa2pre = this.DRAMSET1TMG25.lpddr4_diff_bank_rwa2pre;
      this.DRAMSET1TMG30 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG30::type_id::create("DRAMSET1TMG30",,get_full_name());
      if(this.DRAMSET1TMG30.has_coverage(UVM_CVR_REG_BITS))
      	this.DRAMSET1TMG30.cg_bits.option.name = {get_name(), ".", "DRAMSET1TMG30_bits"};
      this.DRAMSET1TMG30.configure(this, null, "");
      this.DRAMSET1TMG30.build();
	  uvm_resource_db#(string)::set({"REG::", DRAMSET1TMG30.get_full_name()}, "accessType", "NONSECURE", this);
         this.DRAMSET1TMG30.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_mrr2rd", 0, 8},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_mrr2wr", 8, 8},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_mrr2mrw", 16, 8}
         });
      this.default_map.add_reg(this.DRAMSET1TMG30, `UVM_REG_ADDR_WIDTH'h78, "RW", 0);
		this.DRAMSET1TMG30_mrr2rd = this.DRAMSET1TMG30.mrr2rd;
		this.mrr2rd = this.DRAMSET1TMG30.mrr2rd;
		this.DRAMSET1TMG30_mrr2wr = this.DRAMSET1TMG30.mrr2wr;
		this.mrr2wr = this.DRAMSET1TMG30.mrr2wr;
		this.DRAMSET1TMG30_mrr2mrw = this.DRAMSET1TMG30.mrr2mrw;
		this.mrr2mrw = this.DRAMSET1TMG30.mrr2mrw;
      this.DRAMSET1TMG32 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DRAMSET1TMG32::type_id::create("DRAMSET1TMG32",,get_full_name());
      if(this.DRAMSET1TMG32.has_coverage(UVM_CVR_REG_BITS))
      	this.DRAMSET1TMG32.cg_bits.option.name = {get_name(), ".", "DRAMSET1TMG32_bits"};
      this.DRAMSET1TMG32.configure(this, null, "");
      this.DRAMSET1TMG32.build();
	  uvm_resource_db#(string)::set({"REG::", DRAMSET1TMG32.get_full_name()}, "accessType", "NONSECURE", this);
         this.DRAMSET1TMG32.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_ws_fs2wck_sus", 0, 4},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_t_wcksus", 8, 4},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_ws_off2ws_fs", 16, 4}
         });
      this.default_map.add_reg(this.DRAMSET1TMG32, `UVM_REG_ADDR_WIDTH'h80, "RW", 0);
		this.DRAMSET1TMG32_ws_fs2wck_sus = this.DRAMSET1TMG32.ws_fs2wck_sus;
		this.ws_fs2wck_sus = this.DRAMSET1TMG32.ws_fs2wck_sus;
		this.DRAMSET1TMG32_t_wcksus = this.DRAMSET1TMG32.t_wcksus;
		this.t_wcksus = this.DRAMSET1TMG32.t_wcksus;
		this.DRAMSET1TMG32_ws_off2ws_fs = this.DRAMSET1TMG32.ws_off2ws_fs;
		this.ws_off2ws_fs = this.DRAMSET1TMG32.ws_off2ws_fs;
      this.INITMR0 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR0::type_id::create("INITMR0",,get_full_name());
      if(this.INITMR0.has_coverage(UVM_CVR_REG_BITS))
      	this.INITMR0.cg_bits.option.name = {get_name(), ".", "INITMR0_bits"};
      this.INITMR0.configure(this, null, "");
      this.INITMR0.build();
	  uvm_resource_db#(string)::set({"REG::", INITMR0.get_full_name()}, "accessType", "NONSECURE", this);
         this.INITMR0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_emr", 0, 16},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_mr", 16, 16}
         });
      this.default_map.add_reg(this.INITMR0, `UVM_REG_ADDR_WIDTH'h500, "RW", 0);
		this.INITMR0_emr = this.INITMR0.emr;
		this.emr = this.INITMR0.emr;
		this.INITMR0_mr = this.INITMR0.mr;
		this.mr = this.INITMR0.mr;
      this.INITMR1 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR1::type_id::create("INITMR1",,get_full_name());
      if(this.INITMR1.has_coverage(UVM_CVR_REG_BITS))
      	this.INITMR1.cg_bits.option.name = {get_name(), ".", "INITMR1_bits"};
      this.INITMR1.configure(this, null, "");
      this.INITMR1.build();
	  uvm_resource_db#(string)::set({"REG::", INITMR1.get_full_name()}, "accessType", "NONSECURE", this);
         this.INITMR1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_emr3", 0, 16},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_emr2", 16, 16}
         });
      this.default_map.add_reg(this.INITMR1, `UVM_REG_ADDR_WIDTH'h504, "RW", 0);
		this.INITMR1_emr3 = this.INITMR1.emr3;
		this.emr3 = this.INITMR1.emr3;
		this.INITMR1_emr2 = this.INITMR1.emr2;
		this.emr2 = this.INITMR1.emr2;
      this.INITMR2 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR2::type_id::create("INITMR2",,get_full_name());
      if(this.INITMR2.has_coverage(UVM_CVR_REG_BITS))
      	this.INITMR2.cg_bits.option.name = {get_name(), ".", "INITMR2_bits"};
      this.INITMR2.configure(this, null, "");
      this.INITMR2.build();
	  uvm_resource_db#(string)::set({"REG::", INITMR2.get_full_name()}, "accessType", "NONSECURE", this);
         this.INITMR2.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_mr5", 0, 16},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_mr4", 16, 16}
         });
      this.default_map.add_reg(this.INITMR2, `UVM_REG_ADDR_WIDTH'h508, "RW", 0);
		this.INITMR2_mr5 = this.INITMR2.mr5;
		this.mr5 = this.INITMR2.mr5;
		this.INITMR2_mr4 = this.INITMR2.mr4;
		this.mr4 = this.INITMR2.mr4;
      this.INITMR3 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_INITMR3::type_id::create("INITMR3",,get_full_name());
      if(this.INITMR3.has_coverage(UVM_CVR_REG_BITS))
      	this.INITMR3.cg_bits.option.name = {get_name(), ".", "INITMR3_bits"};
      this.INITMR3.configure(this, null, "");
      this.INITMR3.build();
	  uvm_resource_db#(string)::set({"REG::", INITMR3.get_full_name()}, "accessType", "NONSECURE", this);
         this.INITMR3.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_mr6", 0, 16},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_mr22", 16, 16}
         });
      this.default_map.add_reg(this.INITMR3, `UVM_REG_ADDR_WIDTH'h50C, "RW", 0);
		this.INITMR3_mr6 = this.INITMR3.mr6;
		this.mr6 = this.INITMR3.mr6;
		this.INITMR3_mr22 = this.INITMR3.mr22;
		this.mr22 = this.INITMR3.mr22;
      this.DFITMG0 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG0::type_id::create("DFITMG0",,get_full_name());
      if(this.DFITMG0.has_coverage(UVM_CVR_REG_BITS))
      	this.DFITMG0.cg_bits.option.name = {get_name(), ".", "DFITMG0_bits"};
      this.DFITMG0.configure(this, null, "");
      this.DFITMG0.build();
	  uvm_resource_db#(string)::set({"REG::", DFITMG0.get_full_name()}, "accessType", "NONSECURE", this);
         this.DFITMG0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_dfi_tphy_wrlat", 0, 7},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_dfi_tphy_wrdata", 8, 6},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_dfi_t_rddata_en", 16, 7},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_dfi_t_ctrl_delay", 24, 5}
         });
      this.default_map.add_reg(this.DFITMG0, `UVM_REG_ADDR_WIDTH'h580, "RW", 0);
		this.DFITMG0_dfi_tphy_wrlat = this.DFITMG0.dfi_tphy_wrlat;
		this.dfi_tphy_wrlat = this.DFITMG0.dfi_tphy_wrlat;
		this.DFITMG0_dfi_tphy_wrdata = this.DFITMG0.dfi_tphy_wrdata;
		this.dfi_tphy_wrdata = this.DFITMG0.dfi_tphy_wrdata;
		this.DFITMG0_dfi_t_rddata_en = this.DFITMG0.dfi_t_rddata_en;
		this.dfi_t_rddata_en = this.DFITMG0.dfi_t_rddata_en;
		this.DFITMG0_dfi_t_ctrl_delay = this.DFITMG0.dfi_t_ctrl_delay;
		this.dfi_t_ctrl_delay = this.DFITMG0.dfi_t_ctrl_delay;
      this.DFITMG1 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG1::type_id::create("DFITMG1",,get_full_name());
      if(this.DFITMG1.has_coverage(UVM_CVR_REG_BITS))
      	this.DFITMG1.cg_bits.option.name = {get_name(), ".", "DFITMG1_bits"};
      this.DFITMG1.configure(this, null, "");
      this.DFITMG1.build();
	  uvm_resource_db#(string)::set({"REG::", DFITMG1.get_full_name()}, "accessType", "NONSECURE", this);
         this.DFITMG1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_dfi_t_dram_clk_enable", 0, 5},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_dfi_t_dram_clk_disable", 8, 5},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_dfi_t_wrdata_delay", 16, 5}
         });
      this.default_map.add_reg(this.DFITMG1, `UVM_REG_ADDR_WIDTH'h584, "RW", 0);
		this.DFITMG1_dfi_t_dram_clk_enable = this.DFITMG1.dfi_t_dram_clk_enable;
		this.dfi_t_dram_clk_enable = this.DFITMG1.dfi_t_dram_clk_enable;
		this.DFITMG1_dfi_t_dram_clk_disable = this.DFITMG1.dfi_t_dram_clk_disable;
		this.dfi_t_dram_clk_disable = this.DFITMG1.dfi_t_dram_clk_disable;
		this.DFITMG1_dfi_t_wrdata_delay = this.DFITMG1.dfi_t_wrdata_delay;
		this.dfi_t_wrdata_delay = this.DFITMG1.dfi_t_wrdata_delay;
      this.DFITMG2 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG2::type_id::create("DFITMG2",,get_full_name());
      if(this.DFITMG2.has_coverage(UVM_CVR_REG_BITS))
      	this.DFITMG2.cg_bits.option.name = {get_name(), ".", "DFITMG2_bits"};
      this.DFITMG2.configure(this, null, "");
      this.DFITMG2.build();
	  uvm_resource_db#(string)::set({"REG::", DFITMG2.get_full_name()}, "accessType", "NONSECURE", this);
         this.DFITMG2.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_dfi_tphy_wrcslat", 0, 7},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_dfi_tphy_rdcslat", 8, 7},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_dfi_twck_delay", 16, 6}
         });
      this.default_map.add_reg(this.DFITMG2, `UVM_REG_ADDR_WIDTH'h588, "RW", 0);
		this.DFITMG2_dfi_tphy_wrcslat = this.DFITMG2.dfi_tphy_wrcslat;
		this.dfi_tphy_wrcslat = this.DFITMG2.dfi_tphy_wrcslat;
		this.DFITMG2_dfi_tphy_rdcslat = this.DFITMG2.dfi_tphy_rdcslat;
		this.dfi_tphy_rdcslat = this.DFITMG2.dfi_tphy_rdcslat;
		this.DFITMG2_dfi_twck_delay = this.DFITMG2.dfi_twck_delay;
		this.dfi_twck_delay = this.DFITMG2.dfi_twck_delay;
      this.DFITMG4 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG4::type_id::create("DFITMG4",,get_full_name());
      if(this.DFITMG4.has_coverage(UVM_CVR_REG_BITS))
      	this.DFITMG4.cg_bits.option.name = {get_name(), ".", "DFITMG4_bits"};
      this.DFITMG4.configure(this, null, "");
      this.DFITMG4.build();
	  uvm_resource_db#(string)::set({"REG::", DFITMG4.get_full_name()}, "accessType", "NONSECURE", this);
         this.DFITMG4.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_dfi_twck_dis", 0, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_dfi_twck_en_fs", 8, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_dfi_twck_en_wr", 16, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_dfi_twck_en_rd", 24, 8}
         });
      this.default_map.add_reg(this.DFITMG4, `UVM_REG_ADDR_WIDTH'h590, "RW", 0);
		this.DFITMG4_dfi_twck_dis = this.DFITMG4.dfi_twck_dis;
		this.dfi_twck_dis = this.DFITMG4.dfi_twck_dis;
		this.DFITMG4_dfi_twck_en_fs = this.DFITMG4.dfi_twck_en_fs;
		this.dfi_twck_en_fs = this.DFITMG4.dfi_twck_en_fs;
		this.DFITMG4_dfi_twck_en_wr = this.DFITMG4.dfi_twck_en_wr;
		this.dfi_twck_en_wr = this.DFITMG4.dfi_twck_en_wr;
		this.DFITMG4_dfi_twck_en_rd = this.DFITMG4.dfi_twck_en_rd;
		this.dfi_twck_en_rd = this.DFITMG4.dfi_twck_en_rd;
      this.DFITMG5 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG5::type_id::create("DFITMG5",,get_full_name());
      if(this.DFITMG5.has_coverage(UVM_CVR_REG_BITS))
      	this.DFITMG5.cg_bits.option.name = {get_name(), ".", "DFITMG5_bits"};
      this.DFITMG5.configure(this, null, "");
      this.DFITMG5.build();
	  uvm_resource_db#(string)::set({"REG::", DFITMG5.get_full_name()}, "accessType", "NONSECURE", this);
         this.DFITMG5.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_dfi_twck_toggle_post", 0, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_dfi_twck_toggle_cs", 8, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_dfi_twck_toggle", 16, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_dfi_twck_fast_toggle", 24, 8}
         });
      this.default_map.add_reg(this.DFITMG5, `UVM_REG_ADDR_WIDTH'h594, "RW", 0);
		this.DFITMG5_dfi_twck_toggle_post = this.DFITMG5.dfi_twck_toggle_post;
		this.dfi_twck_toggle_post = this.DFITMG5.dfi_twck_toggle_post;
		this.DFITMG5_dfi_twck_toggle_cs = this.DFITMG5.dfi_twck_toggle_cs;
		this.dfi_twck_toggle_cs = this.DFITMG5.dfi_twck_toggle_cs;
		this.DFITMG5_dfi_twck_toggle = this.DFITMG5.dfi_twck_toggle;
		this.dfi_twck_toggle = this.DFITMG5.dfi_twck_toggle;
		this.DFITMG5_dfi_twck_fast_toggle = this.DFITMG5.dfi_twck_fast_toggle;
		this.dfi_twck_fast_toggle = this.DFITMG5.dfi_twck_fast_toggle;
      this.DFITMG6 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFITMG6::type_id::create("DFITMG6",,get_full_name());
      if(this.DFITMG6.has_coverage(UVM_CVR_REG_BITS))
      	this.DFITMG6.cg_bits.option.name = {get_name(), ".", "DFITMG6_bits"};
      this.DFITMG6.configure(this, null, "");
      this.DFITMG6.build();
	  uvm_resource_db#(string)::set({"REG::", DFITMG6.get_full_name()}, "accessType", "NONSECURE", this);
         this.DFITMG6.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_dfi_twck_toggle_post_rd", 0, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_dfi_twck_toggle_post_rd_en", 8, 1}
         });
      this.default_map.add_reg(this.DFITMG6, `UVM_REG_ADDR_WIDTH'h598, "RW", 0);
		this.DFITMG6_dfi_twck_toggle_post_rd = this.DFITMG6.dfi_twck_toggle_post_rd;
		this.dfi_twck_toggle_post_rd = this.DFITMG6.dfi_twck_toggle_post_rd;
		this.DFITMG6_dfi_twck_toggle_post_rd_en = this.DFITMG6.dfi_twck_toggle_post_rd_en;
		this.dfi_twck_toggle_post_rd_en = this.DFITMG6.dfi_twck_toggle_post_rd_en;
      this.DFILPTMG0 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFILPTMG0::type_id::create("DFILPTMG0",,get_full_name());
      if(this.DFILPTMG0.has_coverage(UVM_CVR_REG_BITS))
      	this.DFILPTMG0.cg_bits.option.name = {get_name(), ".", "DFILPTMG0_bits"};
      this.DFILPTMG0.configure(this, null, "");
      this.DFILPTMG0.build();
	  uvm_resource_db#(string)::set({"REG::", DFILPTMG0.get_full_name()}, "accessType", "NONSECURE", this);
         this.DFILPTMG0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_dfi_lp_wakeup_pd", 0, 5},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_dfi_lp_wakeup_sr", 8, 5},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_dfi_lp_wakeup_dsm", 16, 5}
         });
      this.default_map.add_reg(this.DFILPTMG0, `UVM_REG_ADDR_WIDTH'h5A0, "RW", 0);
		this.DFILPTMG0_dfi_lp_wakeup_pd = this.DFILPTMG0.dfi_lp_wakeup_pd;
		this.dfi_lp_wakeup_pd = this.DFILPTMG0.dfi_lp_wakeup_pd;
		this.DFILPTMG0_dfi_lp_wakeup_sr = this.DFILPTMG0.dfi_lp_wakeup_sr;
		this.dfi_lp_wakeup_sr = this.DFILPTMG0.dfi_lp_wakeup_sr;
		this.DFILPTMG0_dfi_lp_wakeup_dsm = this.DFILPTMG0.dfi_lp_wakeup_dsm;
		this.dfi_lp_wakeup_dsm = this.DFILPTMG0.dfi_lp_wakeup_dsm;
      this.DFILPTMG1 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFILPTMG1::type_id::create("DFILPTMG1",,get_full_name());
      if(this.DFILPTMG1.has_coverage(UVM_CVR_REG_BITS))
      	this.DFILPTMG1.cg_bits.option.name = {get_name(), ".", "DFILPTMG1_bits"};
      this.DFILPTMG1.configure(this, null, "");
      this.DFILPTMG1.build();
	  uvm_resource_db#(string)::set({"REG::", DFILPTMG1.get_full_name()}, "accessType", "NONSECURE", this);
         this.DFILPTMG1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_dfi_lp_wakeup_data", 0, 5},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_dfi_tlp_resp", 8, 5}
         });
      this.default_map.add_reg(this.DFILPTMG1, `UVM_REG_ADDR_WIDTH'h5A4, "RW", 0);
		this.DFILPTMG1_dfi_lp_wakeup_data = this.DFILPTMG1.dfi_lp_wakeup_data;
		this.dfi_lp_wakeup_data = this.DFILPTMG1.dfi_lp_wakeup_data;
		this.DFILPTMG1_dfi_tlp_resp = this.DFILPTMG1.dfi_tlp_resp;
		this.dfi_tlp_resp = this.DFILPTMG1.dfi_tlp_resp;
      this.DFIUPDTMG0 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG0::type_id::create("DFIUPDTMG0",,get_full_name());
      if(this.DFIUPDTMG0.has_coverage(UVM_CVR_REG_BITS))
      	this.DFIUPDTMG0.cg_bits.option.name = {get_name(), ".", "DFIUPDTMG0_bits"};
      this.DFIUPDTMG0.configure(this, null, "");
      this.DFIUPDTMG0.build();
	  uvm_resource_db#(string)::set({"REG::", DFIUPDTMG0.get_full_name()}, "accessType", "NONSECURE", this);
         this.DFIUPDTMG0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_dfi_t_ctrlup_min", 0, 10},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_dfi_t_ctrlup_max", 16, 10}
         });
      this.default_map.add_reg(this.DFIUPDTMG0, `UVM_REG_ADDR_WIDTH'h5A8, "RW", 0);
		this.DFIUPDTMG0_dfi_t_ctrlup_min = this.DFIUPDTMG0.dfi_t_ctrlup_min;
		this.dfi_t_ctrlup_min = this.DFIUPDTMG0.dfi_t_ctrlup_min;
		this.DFIUPDTMG0_dfi_t_ctrlup_max = this.DFIUPDTMG0.dfi_t_ctrlup_max;
		this.dfi_t_ctrlup_max = this.DFIUPDTMG0.dfi_t_ctrlup_max;
      this.DFIUPDTMG1 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG1::type_id::create("DFIUPDTMG1",,get_full_name());
      if(this.DFIUPDTMG1.has_coverage(UVM_CVR_REG_BITS))
      	this.DFIUPDTMG1.cg_bits.option.name = {get_name(), ".", "DFIUPDTMG1_bits"};
      this.DFIUPDTMG1.configure(this, null, "");
      this.DFIUPDTMG1.build();
	  uvm_resource_db#(string)::set({"REG::", DFIUPDTMG1.get_full_name()}, "accessType", "NONSECURE", this);
         this.DFIUPDTMG1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_dfi_t_ctrlupd_interval_max_x1024", 0, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_dfi_t_ctrlupd_interval_min_x1024", 16, 8}
         });
      this.default_map.add_reg(this.DFIUPDTMG1, `UVM_REG_ADDR_WIDTH'h5AC, "RW", 0);
		this.DFIUPDTMG1_dfi_t_ctrlupd_interval_max_x1024 = this.DFIUPDTMG1.dfi_t_ctrlupd_interval_max_x1024;
		this.dfi_t_ctrlupd_interval_max_x1024 = this.DFIUPDTMG1.dfi_t_ctrlupd_interval_max_x1024;
		this.DFIUPDTMG1_dfi_t_ctrlupd_interval_min_x1024 = this.DFIUPDTMG1.dfi_t_ctrlupd_interval_min_x1024;
		this.dfi_t_ctrlupd_interval_min_x1024 = this.DFIUPDTMG1.dfi_t_ctrlupd_interval_min_x1024;
      this.DFIUPDTMG2 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG2::type_id::create("DFIUPDTMG2",,get_full_name());
      if(this.DFIUPDTMG2.has_coverage(UVM_CVR_REG_BITS))
      	this.DFIUPDTMG2.cg_bits.option.name = {get_name(), ".", "DFIUPDTMG2_bits"};
      this.DFIUPDTMG2.configure(this, null, "");
      this.DFIUPDTMG2.build();
	  uvm_resource_db#(string)::set({"REG::", DFIUPDTMG2.get_full_name()}, "accessType", "NONSECURE", this);
         this.DFIUPDTMG2.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_dfi_t_ctrlupd_interval_type1", 0, 12},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_ctrlupd_after_dqsosc", 27, 1},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_ppt2_override", 28, 1},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_ppt2_en", 29, 1},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_dfi_t_ctrlupd_interval_type1_unit", 30, 2}
         });
      this.default_map.add_reg(this.DFIUPDTMG2, `UVM_REG_ADDR_WIDTH'h5B4, "RW", 0);
		this.DFIUPDTMG2_dfi_t_ctrlupd_interval_type1 = this.DFIUPDTMG2.dfi_t_ctrlupd_interval_type1;
		this.dfi_t_ctrlupd_interval_type1 = this.DFIUPDTMG2.dfi_t_ctrlupd_interval_type1;
		this.DFIUPDTMG2_ctrlupd_after_dqsosc = this.DFIUPDTMG2.ctrlupd_after_dqsosc;
		this.ctrlupd_after_dqsosc = this.DFIUPDTMG2.ctrlupd_after_dqsosc;
		this.DFIUPDTMG2_ppt2_override = this.DFIUPDTMG2.ppt2_override;
		this.ppt2_override = this.DFIUPDTMG2.ppt2_override;
		this.DFIUPDTMG2_ppt2_en = this.DFIUPDTMG2.ppt2_en;
		this.ppt2_en = this.DFIUPDTMG2.ppt2_en;
		this.DFIUPDTMG2_dfi_t_ctrlupd_interval_type1_unit = this.DFIUPDTMG2.dfi_t_ctrlupd_interval_type1_unit;
		this.dfi_t_ctrlupd_interval_type1_unit = this.DFIUPDTMG2.dfi_t_ctrlupd_interval_type1_unit;
      this.DFIUPDTMG3 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DFIUPDTMG3::type_id::create("DFIUPDTMG3",,get_full_name());
      if(this.DFIUPDTMG3.has_coverage(UVM_CVR_REG_BITS))
      	this.DFIUPDTMG3.cg_bits.option.name = {get_name(), ".", "DFIUPDTMG3_bits"};
      this.DFIUPDTMG3.configure(this, null, "");
      this.DFIUPDTMG3.build();
	  uvm_resource_db#(string)::set({"REG::", DFIUPDTMG3.get_full_name()}, "accessType", "NONSECURE", this);
         this.DFIUPDTMG3.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_dfi_t_ctrlupd_burst_interval_x8", 0, 9}
         });
      this.default_map.add_reg(this.DFIUPDTMG3, `UVM_REG_ADDR_WIDTH'h5B8, "RW", 0);
		this.DFIUPDTMG3_dfi_t_ctrlupd_burst_interval_x8 = this.DFIUPDTMG3.dfi_t_ctrlupd_burst_interval_x8;
		this.dfi_t_ctrlupd_burst_interval_x8 = this.DFIUPDTMG3.dfi_t_ctrlupd_burst_interval_x8;
      this.RFSHSET1TMG0 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG0::type_id::create("RFSHSET1TMG0",,get_full_name());
      if(this.RFSHSET1TMG0.has_coverage(UVM_CVR_REG_BITS))
      	this.RFSHSET1TMG0.cg_bits.option.name = {get_name(), ".", "RFSHSET1TMG0_bits"};
      this.RFSHSET1TMG0.configure(this, null, "");
      this.RFSHSET1TMG0.build();
	  uvm_resource_db#(string)::set({"REG::", RFSHSET1TMG0.get_full_name()}, "accessType", "NONSECURE", this);
         this.RFSHSET1TMG0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_t_refi_x1_x32", 0, 14},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_refresh_to_x1_x32", 16, 6},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_refresh_margin", 24, 4},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_refresh_to_x1_sel", 30, 1},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_t_refi_x1_sel", 31, 1}
         });
      this.default_map.add_reg(this.RFSHSET1TMG0, `UVM_REG_ADDR_WIDTH'h600, "RW", 0);
		this.RFSHSET1TMG0_t_refi_x1_x32 = this.RFSHSET1TMG0.t_refi_x1_x32;
		this.t_refi_x1_x32 = this.RFSHSET1TMG0.t_refi_x1_x32;
		this.RFSHSET1TMG0_refresh_to_x1_x32 = this.RFSHSET1TMG0.refresh_to_x1_x32;
		this.refresh_to_x1_x32 = this.RFSHSET1TMG0.refresh_to_x1_x32;
		this.RFSHSET1TMG0_refresh_margin = this.RFSHSET1TMG0.refresh_margin;
		this.refresh_margin = this.RFSHSET1TMG0.refresh_margin;
		this.RFSHSET1TMG0_refresh_to_x1_sel = this.RFSHSET1TMG0.refresh_to_x1_sel;
		this.refresh_to_x1_sel = this.RFSHSET1TMG0.refresh_to_x1_sel;
		this.RFSHSET1TMG0_t_refi_x1_sel = this.RFSHSET1TMG0.t_refi_x1_sel;
		this.t_refi_x1_sel = this.RFSHSET1TMG0.t_refi_x1_sel;
      this.RFSHSET1TMG1 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG1::type_id::create("RFSHSET1TMG1",,get_full_name());
      if(this.RFSHSET1TMG1.has_coverage(UVM_CVR_REG_BITS))
      	this.RFSHSET1TMG1.cg_bits.option.name = {get_name(), ".", "RFSHSET1TMG1_bits"};
      this.RFSHSET1TMG1.configure(this, null, "");
      this.RFSHSET1TMG1.build();
	  uvm_resource_db#(string)::set({"REG::", RFSHSET1TMG1.get_full_name()}, "accessType", "NONSECURE", this);
         this.RFSHSET1TMG1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_t_rfc_min", 0, 12},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_t_rfc_min_ab", 16, 12}
         });
      this.default_map.add_reg(this.RFSHSET1TMG1, `UVM_REG_ADDR_WIDTH'h604, "RW", 0);
		this.RFSHSET1TMG1_t_rfc_min = this.RFSHSET1TMG1.t_rfc_min;
		this.t_rfc_min = this.RFSHSET1TMG1.t_rfc_min;
		this.RFSHSET1TMG1_t_rfc_min_ab = this.RFSHSET1TMG1.t_rfc_min_ab;
		this.t_rfc_min_ab = this.RFSHSET1TMG1.t_rfc_min_ab;
      this.RFSHSET1TMG2 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG2::type_id::create("RFSHSET1TMG2",,get_full_name());
      if(this.RFSHSET1TMG2.has_coverage(UVM_CVR_REG_BITS))
      	this.RFSHSET1TMG2.cg_bits.option.name = {get_name(), ".", "RFSHSET1TMG2_bits"};
      this.RFSHSET1TMG2.configure(this, null, "");
      this.RFSHSET1TMG2.build();
	  uvm_resource_db#(string)::set({"REG::", RFSHSET1TMG2.get_full_name()}, "accessType", "NONSECURE", this);
         this.RFSHSET1TMG2.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_t_pbr2pbr", 16, 8},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_t_pbr2act", 24, 8}
         });
      this.default_map.add_reg(this.RFSHSET1TMG2, `UVM_REG_ADDR_WIDTH'h608, "RW", 0);
		this.RFSHSET1TMG2_t_pbr2pbr = this.RFSHSET1TMG2.t_pbr2pbr;
		this.t_pbr2pbr = this.RFSHSET1TMG2.t_pbr2pbr;
		this.RFSHSET1TMG2_t_pbr2act = this.RFSHSET1TMG2.t_pbr2act;
		this.t_pbr2act = this.RFSHSET1TMG2.t_pbr2act;
      this.RFSHSET1TMG3 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG3::type_id::create("RFSHSET1TMG3",,get_full_name());
      if(this.RFSHSET1TMG3.has_coverage(UVM_CVR_REG_BITS))
      	this.RFSHSET1TMG3.cg_bits.option.name = {get_name(), ".", "RFSHSET1TMG3_bits"};
      this.RFSHSET1TMG3.configure(this, null, "");
      this.RFSHSET1TMG3.build();
	  uvm_resource_db#(string)::set({"REG::", RFSHSET1TMG3.get_full_name()}, "accessType", "NONSECURE", this);
         this.RFSHSET1TMG3.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_refresh_to_ab_x32", 24, 6}
         });
      this.default_map.add_reg(this.RFSHSET1TMG3, `UVM_REG_ADDR_WIDTH'h60C, "RW", 0);
		this.RFSHSET1TMG3_refresh_to_ab_x32 = this.RFSHSET1TMG3.refresh_to_ab_x32;
		this.refresh_to_ab_x32 = this.RFSHSET1TMG3.refresh_to_ab_x32;
      this.RFSHSET1TMG4 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFSHSET1TMG4::type_id::create("RFSHSET1TMG4",,get_full_name());
      if(this.RFSHSET1TMG4.has_coverage(UVM_CVR_REG_BITS))
      	this.RFSHSET1TMG4.cg_bits.option.name = {get_name(), ".", "RFSHSET1TMG4_bits"};
      this.RFSHSET1TMG4.configure(this, null, "");
      this.RFSHSET1TMG4.build();
	  uvm_resource_db#(string)::set({"REG::", RFSHSET1TMG4.get_full_name()}, "accessType", "NONSECURE", this);
         this.RFSHSET1TMG4.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_refresh_timer0_start_value_x32", 0, 12},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_refresh_timer1_start_value_x32", 16, 12}
         });
      this.default_map.add_reg(this.RFSHSET1TMG4, `UVM_REG_ADDR_WIDTH'h610, "RW", 0);
		this.RFSHSET1TMG4_refresh_timer0_start_value_x32 = this.RFSHSET1TMG4.refresh_timer0_start_value_x32;
		this.refresh_timer0_start_value_x32 = this.RFSHSET1TMG4.refresh_timer0_start_value_x32;
		this.RFSHSET1TMG4_refresh_timer1_start_value_x32 = this.RFSHSET1TMG4.refresh_timer1_start_value_x32;
		this.refresh_timer1_start_value_x32 = this.RFSHSET1TMG4.refresh_timer1_start_value_x32;
      this.RFMSET1TMG0 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RFMSET1TMG0::type_id::create("RFMSET1TMG0",,get_full_name());
      if(this.RFMSET1TMG0.has_coverage(UVM_CVR_REG_BITS))
      	this.RFMSET1TMG0.cg_bits.option.name = {get_name(), ".", "RFMSET1TMG0_bits"};
      this.RFMSET1TMG0.configure(this, null, "");
      this.RFMSET1TMG0.build();
	  uvm_resource_db#(string)::set({"REG::", RFMSET1TMG0.get_full_name()}, "accessType", "NONSECURE", this);
         this.RFMSET1TMG0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_t_rfmpb", 0, 12}
         });
      this.default_map.add_reg(this.RFMSET1TMG0, `UVM_REG_ADDR_WIDTH'h650, "RW", 0);
		this.RFMSET1TMG0_t_rfmpb = this.RFMSET1TMG0.t_rfmpb;
		this.t_rfmpb = this.RFMSET1TMG0.t_rfmpb;
      this.ZQSET1TMG0 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_ZQSET1TMG0::type_id::create("ZQSET1TMG0",,get_full_name());
      if(this.ZQSET1TMG0.has_coverage(UVM_CVR_REG_BITS))
      	this.ZQSET1TMG0.cg_bits.option.name = {get_name(), ".", "ZQSET1TMG0_bits"};
      this.ZQSET1TMG0.configure(this, null, "");
      this.ZQSET1TMG0.build();
	  uvm_resource_db#(string)::set({"REG::", ZQSET1TMG0.get_full_name()}, "accessType", "NONSECURE", this);
         this.ZQSET1TMG0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_t_zq_long_nop", 0, 14},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_t_zq_short_nop", 16, 10}
         });
      this.default_map.add_reg(this.ZQSET1TMG0, `UVM_REG_ADDR_WIDTH'h800, "RW", 0);
		this.ZQSET1TMG0_t_zq_long_nop = this.ZQSET1TMG0.t_zq_long_nop;
		this.t_zq_long_nop = this.ZQSET1TMG0.t_zq_long_nop;
		this.ZQSET1TMG0_t_zq_short_nop = this.ZQSET1TMG0.t_zq_short_nop;
		this.t_zq_short_nop = this.ZQSET1TMG0.t_zq_short_nop;
      this.ZQSET1TMG1 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_ZQSET1TMG1::type_id::create("ZQSET1TMG1",,get_full_name());
      if(this.ZQSET1TMG1.has_coverage(UVM_CVR_REG_BITS))
      	this.ZQSET1TMG1.cg_bits.option.name = {get_name(), ".", "ZQSET1TMG1_bits"};
      this.ZQSET1TMG1.configure(this, null, "");
      this.ZQSET1TMG1.build();
	  uvm_resource_db#(string)::set({"REG::", ZQSET1TMG1.get_full_name()}, "accessType", "NONSECURE", this);
         this.ZQSET1TMG1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_zq_short_interval_x1024", 0, 20},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_zq_reset_nop", 20, 10}
         });
      this.default_map.add_reg(this.ZQSET1TMG1, `UVM_REG_ADDR_WIDTH'h804, "RW", 0);
		this.ZQSET1TMG1_t_zq_short_interval_x1024 = this.ZQSET1TMG1.t_zq_short_interval_x1024;
		this.t_zq_short_interval_x1024 = this.ZQSET1TMG1.t_zq_short_interval_x1024;
		this.ZQSET1TMG1_t_zq_reset_nop = this.ZQSET1TMG1.t_zq_reset_nop;
		this.t_zq_reset_nop = this.ZQSET1TMG1.t_zq_reset_nop;
      this.ZQSET1TMG2 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_ZQSET1TMG2::type_id::create("ZQSET1TMG2",,get_full_name());
      if(this.ZQSET1TMG2.has_coverage(UVM_CVR_REG_BITS))
      	this.ZQSET1TMG2.cg_bits.option.name = {get_name(), ".", "ZQSET1TMG2_bits"};
      this.ZQSET1TMG2.configure(this, null, "");
      this.ZQSET1TMG2.build();
	  uvm_resource_db#(string)::set({"REG::", ZQSET1TMG2.get_full_name()}, "accessType", "NONSECURE", this);
         this.ZQSET1TMG2.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_t_zq_stop", 0, 7}
         });
      this.default_map.add_reg(this.ZQSET1TMG2, `UVM_REG_ADDR_WIDTH'h808, "RW", 0);
		this.ZQSET1TMG2_t_zq_stop = this.ZQSET1TMG2.t_zq_stop;
		this.t_zq_stop = this.ZQSET1TMG2.t_zq_stop;
      this.DQSOSCCTL0 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DQSOSCCTL0::type_id::create("DQSOSCCTL0",,get_full_name());
      if(this.DQSOSCCTL0.has_coverage(UVM_CVR_REG_BITS))
      	this.DQSOSCCTL0.cg_bits.option.name = {get_name(), ".", "DQSOSCCTL0_bits"};
      this.DQSOSCCTL0.configure(this, null, "");
      this.DQSOSCCTL0.build();
	  uvm_resource_db#(string)::set({"REG::", DQSOSCCTL0.get_full_name()}, "accessType", "NONSECURE", this);
         this.DQSOSCCTL0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_dqsosc_enable", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_dqsosc_interval_unit", 2, 1},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_dqsosc_interval", 4, 12}
         });
      this.default_map.add_reg(this.DQSOSCCTL0, `UVM_REG_ADDR_WIDTH'hA80, "RW", 0);
		this.DQSOSCCTL0_dqsosc_enable = this.DQSOSCCTL0.dqsosc_enable;
		this.dqsosc_enable = this.DQSOSCCTL0.dqsosc_enable;
		this.DQSOSCCTL0_dqsosc_interval_unit = this.DQSOSCCTL0.dqsosc_interval_unit;
		this.dqsosc_interval_unit = this.DQSOSCCTL0.dqsosc_interval_unit;
		this.DQSOSCCTL0_dqsosc_interval = this.DQSOSCCTL0.dqsosc_interval;
		this.dqsosc_interval = this.DQSOSCCTL0.dqsosc_interval;
      this.DERATEINT = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DERATEINT::type_id::create("DERATEINT",,get_full_name());
      if(this.DERATEINT.has_coverage(UVM_CVR_REG_BITS))
      	this.DERATEINT.cg_bits.option.name = {get_name(), ".", "DERATEINT_bits"};
      this.DERATEINT.configure(this, null, "");
      this.DERATEINT.build();
	  uvm_resource_db#(string)::set({"REG::", DERATEINT.get_full_name()}, "accessType", "NONSECURE", this);
         this.DERATEINT.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_mr4_read_interval", 0, 32}
         });
      this.default_map.add_reg(this.DERATEINT, `UVM_REG_ADDR_WIDTH'hB00, "RW", 0);
		this.DERATEINT_mr4_read_interval = this.DERATEINT.mr4_read_interval;
		this.mr4_read_interval = this.DERATEINT.mr4_read_interval;
      this.DERATEVAL0 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DERATEVAL0::type_id::create("DERATEVAL0",,get_full_name());
      if(this.DERATEVAL0.has_coverage(UVM_CVR_REG_BITS))
      	this.DERATEVAL0.cg_bits.option.name = {get_name(), ".", "DERATEVAL0_bits"};
      this.DERATEVAL0.configure(this, null, "");
      this.DERATEVAL0.build();
	  uvm_resource_db#(string)::set({"REG::", DERATEVAL0.get_full_name()}, "accessType", "NONSECURE", this);
         this.DERATEVAL0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_derated_t_rrd", 0, 6},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_derated_t_rp", 8, 7},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_derated_t_ras_min", 16, 8},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_derated_t_rcd", 24, 8}
         });
      this.default_map.add_reg(this.DERATEVAL0, `UVM_REG_ADDR_WIDTH'hB04, "RW", 0);
		this.DERATEVAL0_derated_t_rrd = this.DERATEVAL0.derated_t_rrd;
		this.derated_t_rrd = this.DERATEVAL0.derated_t_rrd;
		this.DERATEVAL0_derated_t_rp = this.DERATEVAL0.derated_t_rp;
		this.derated_t_rp = this.DERATEVAL0.derated_t_rp;
		this.DERATEVAL0_derated_t_ras_min = this.DERATEVAL0.derated_t_ras_min;
		this.derated_t_ras_min = this.DERATEVAL0.derated_t_ras_min;
		this.DERATEVAL0_derated_t_rcd = this.DERATEVAL0.derated_t_rcd;
		this.derated_t_rcd = this.DERATEVAL0.derated_t_rcd;
      this.DERATEVAL1 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DERATEVAL1::type_id::create("DERATEVAL1",,get_full_name());
      if(this.DERATEVAL1.has_coverage(UVM_CVR_REG_BITS))
      	this.DERATEVAL1.cg_bits.option.name = {get_name(), ".", "DERATEVAL1_bits"};
      this.DERATEVAL1.configure(this, null, "");
      this.DERATEVAL1.build();
	  uvm_resource_db#(string)::set({"REG::", DERATEVAL1.get_full_name()}, "accessType", "NONSECURE", this);
         this.DERATEVAL1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_derated_t_rc", 0, 8},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_derated_t_rcd_write", 8, 8}
         });
      this.default_map.add_reg(this.DERATEVAL1, `UVM_REG_ADDR_WIDTH'hB08, "RW", 0);
		this.DERATEVAL1_derated_t_rc = this.DERATEVAL1.derated_t_rc;
		this.derated_t_rc = this.DERATEVAL1.derated_t_rc;
		this.DERATEVAL1_derated_t_rcd_write = this.DERATEVAL1.derated_t_rcd_write;
		this.derated_t_rcd_write = this.DERATEVAL1.derated_t_rcd_write;
      this.HWLPTMG0 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_HWLPTMG0::type_id::create("HWLPTMG0",,get_full_name());
      if(this.HWLPTMG0.has_coverage(UVM_CVR_REG_BITS))
      	this.HWLPTMG0.cg_bits.option.name = {get_name(), ".", "HWLPTMG0_bits"};
      this.HWLPTMG0.configure(this, null, "");
      this.HWLPTMG0.build();
	  uvm_resource_db#(string)::set({"REG::", HWLPTMG0.get_full_name()}, "accessType", "NONSECURE", this);
         this.HWLPTMG0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_hw_lp_idle_x32", 16, 12}
         });
      this.default_map.add_reg(this.HWLPTMG0, `UVM_REG_ADDR_WIDTH'hB80, "RW", 0);
		this.HWLPTMG0_hw_lp_idle_x32 = this.HWLPTMG0.hw_lp_idle_x32;
		this.hw_lp_idle_x32 = this.HWLPTMG0.hw_lp_idle_x32;
      this.DVFSCTL0 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DVFSCTL0::type_id::create("DVFSCTL0",,get_full_name());
      if(this.DVFSCTL0.has_coverage(UVM_CVR_REG_BITS))
      	this.DVFSCTL0.cg_bits.option.name = {get_name(), ".", "DVFSCTL0_bits"};
      this.DVFSCTL0.configure(this, null, "");
      this.DVFSCTL0.build();
	  uvm_resource_db#(string)::set({"REG::", DVFSCTL0.get_full_name()}, "accessType", "NONSECURE", this);
         this.DVFSCTL0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_dvfsq_enable", 2, 1}
         });
      this.default_map.add_reg(this.DVFSCTL0, `UVM_REG_ADDR_WIDTH'hB84, "RW", 0);
		this.DVFSCTL0_dvfsq_enable = this.DVFSCTL0.dvfsq_enable;
		this.dvfsq_enable = this.DVFSCTL0.dvfsq_enable;
      this.SCHEDTMG0 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_SCHEDTMG0::type_id::create("SCHEDTMG0",,get_full_name());
      if(this.SCHEDTMG0.has_coverage(UVM_CVR_REG_BITS))
      	this.SCHEDTMG0.cg_bits.option.name = {get_name(), ".", "SCHEDTMG0_bits"};
      this.SCHEDTMG0.configure(this, null, "");
      this.SCHEDTMG0.build();
	  uvm_resource_db#(string)::set({"REG::", SCHEDTMG0.get_full_name()}, "accessType", "NONSECURE", this);
         this.SCHEDTMG0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_pageclose_timer", 0, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_rdwr_idle_gap", 8, 7}
         });
      this.default_map.add_reg(this.SCHEDTMG0, `UVM_REG_ADDR_WIDTH'hC00, "RW", 0);
		this.SCHEDTMG0_pageclose_timer = this.SCHEDTMG0.pageclose_timer;
		this.pageclose_timer = this.SCHEDTMG0.pageclose_timer;
		this.SCHEDTMG0_rdwr_idle_gap = this.SCHEDTMG0.rdwr_idle_gap;
		this.rdwr_idle_gap = this.SCHEDTMG0.rdwr_idle_gap;
      this.PERFHPR1 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_PERFHPR1::type_id::create("PERFHPR1",,get_full_name());
      if(this.PERFHPR1.has_coverage(UVM_CVR_REG_BITS))
      	this.PERFHPR1.cg_bits.option.name = {get_name(), ".", "PERFHPR1_bits"};
      this.PERFHPR1.configure(this, null, "");
      this.PERFHPR1.build();
	  uvm_resource_db#(string)::set({"REG::", PERFHPR1.get_full_name()}, "accessType", "NONSECURE", this);
         this.PERFHPR1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_hpr_max_starve", 0, 16},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_hpr_xact_run_length", 24, 8}
         });
      this.default_map.add_reg(this.PERFHPR1, `UVM_REG_ADDR_WIDTH'hC80, "RW", 0);
		this.PERFHPR1_hpr_max_starve = this.PERFHPR1.hpr_max_starve;
		this.hpr_max_starve = this.PERFHPR1.hpr_max_starve;
		this.PERFHPR1_hpr_xact_run_length = this.PERFHPR1.hpr_xact_run_length;
		this.hpr_xact_run_length = this.PERFHPR1.hpr_xact_run_length;
      this.PERFLPR1 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_PERFLPR1::type_id::create("PERFLPR1",,get_full_name());
      if(this.PERFLPR1.has_coverage(UVM_CVR_REG_BITS))
      	this.PERFLPR1.cg_bits.option.name = {get_name(), ".", "PERFLPR1_bits"};
      this.PERFLPR1.configure(this, null, "");
      this.PERFLPR1.build();
	  uvm_resource_db#(string)::set({"REG::", PERFLPR1.get_full_name()}, "accessType", "NONSECURE", this);
         this.PERFLPR1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_lpr_max_starve", 0, 16},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_lpr_xact_run_length", 24, 8}
         });
      this.default_map.add_reg(this.PERFLPR1, `UVM_REG_ADDR_WIDTH'hC84, "RW", 0);
		this.PERFLPR1_lpr_max_starve = this.PERFLPR1.lpr_max_starve;
		this.lpr_max_starve = this.PERFLPR1.lpr_max_starve;
		this.PERFLPR1_lpr_xact_run_length = this.PERFLPR1.lpr_xact_run_length;
		this.lpr_xact_run_length = this.PERFLPR1.lpr_xact_run_length;
      this.PERFWR1 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_PERFWR1::type_id::create("PERFWR1",,get_full_name());
      if(this.PERFWR1.has_coverage(UVM_CVR_REG_BITS))
      	this.PERFWR1.cg_bits.option.name = {get_name(), ".", "PERFWR1_bits"};
      this.PERFWR1.configure(this, null, "");
      this.PERFWR1.build();
	  uvm_resource_db#(string)::set({"REG::", PERFWR1.get_full_name()}, "accessType", "NONSECURE", this);
         this.PERFWR1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_w_max_starve", 0, 16},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_w_xact_run_length", 24, 8}
         });
      this.default_map.add_reg(this.PERFWR1, `UVM_REG_ADDR_WIDTH'hC88, "RW", 0);
		this.PERFWR1_w_max_starve = this.PERFWR1.w_max_starve;
		this.w_max_starve = this.PERFWR1.w_max_starve;
		this.PERFWR1_w_xact_run_length = this.PERFWR1.w_xact_run_length;
		this.w_xact_run_length = this.PERFWR1.w_xact_run_length;
      this.TMGCFG = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_TMGCFG::type_id::create("TMGCFG",,get_full_name());
      if(this.TMGCFG.has_coverage(UVM_CVR_REG_BITS))
      	this.TMGCFG.cg_bits.option.name = {get_name(), ".", "TMGCFG_bits"};
      this.TMGCFG.configure(this, null, "");
      this.TMGCFG.build();
	  uvm_resource_db#(string)::set({"REG::", TMGCFG.get_full_name()}, "accessType", "NONSECURE", this);
         this.TMGCFG.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_frequency_ratio", 0, 1}
         });
      this.default_map.add_reg(this.TMGCFG, `UVM_REG_ADDR_WIDTH'hD00, "RW", 0);
		this.TMGCFG_frequency_ratio = this.TMGCFG.frequency_ratio;
		this.frequency_ratio = this.TMGCFG.frequency_ratio;
      this.RANKTMG0 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RANKTMG0::type_id::create("RANKTMG0",,get_full_name());
      if(this.RANKTMG0.has_coverage(UVM_CVR_REG_BITS))
      	this.RANKTMG0.cg_bits.option.name = {get_name(), ".", "RANKTMG0_bits"};
      this.RANKTMG0.configure(this, null, "");
      this.RANKTMG0.build();
	  uvm_resource_db#(string)::set({"REG::", RANKTMG0.get_full_name()}, "accessType", "NONSECURE", this);
         this.RANKTMG0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_diff_rank_rd_gap", 0, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_diff_rank_wr_gap", 8, 8}
         });
      this.default_map.add_reg(this.RANKTMG0, `UVM_REG_ADDR_WIDTH'hD04, "RW", 0);
		this.RANKTMG0_diff_rank_rd_gap = this.RANKTMG0.diff_rank_rd_gap;
		this.diff_rank_rd_gap = this.RANKTMG0.diff_rank_rd_gap;
		this.RANKTMG0_diff_rank_wr_gap = this.RANKTMG0.diff_rank_wr_gap;
		this.diff_rank_wr_gap = this.RANKTMG0.diff_rank_wr_gap;
      this.RANKTMG1 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_RANKTMG1::type_id::create("RANKTMG1",,get_full_name());
      if(this.RANKTMG1.has_coverage(UVM_CVR_REG_BITS))
      	this.RANKTMG1.cg_bits.option.name = {get_name(), ".", "RANKTMG1_bits"};
      this.RANKTMG1.configure(this, null, "");
      this.RANKTMG1.build();
	  uvm_resource_db#(string)::set({"REG::", RANKTMG1.get_full_name()}, "accessType", "NONSECURE", this);
         this.RANKTMG1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_wr2rd_dr", 0, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_rd2wr_dr", 8, 8}
         });
      this.default_map.add_reg(this.RANKTMG1, `UVM_REG_ADDR_WIDTH'hD08, "RW", 0);
		this.RANKTMG1_wr2rd_dr = this.RANKTMG1.wr2rd_dr;
		this.wr2rd_dr = this.RANKTMG1.wr2rd_dr;
		this.RANKTMG1_rd2wr_dr = this.RANKTMG1.rd2wr_dr;
		this.rd2wr_dr = this.RANKTMG1.rd2wr_dr;
      this.PWRTMG = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_PWRTMG::type_id::create("PWRTMG",,get_full_name());
      if(this.PWRTMG.has_coverage(UVM_CVR_REG_BITS))
      	this.PWRTMG.cg_bits.option.name = {get_name(), ".", "PWRTMG_bits"};
      this.PWRTMG.configure(this, null, "");
      this.PWRTMG.build();
	  uvm_resource_db#(string)::set({"REG::", PWRTMG.get_full_name()}, "accessType", "NONSECURE", this);
         this.PWRTMG.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_powerdown_to_x32", 0, 7},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_selfref_to_x32", 16, 10}
         });
      this.default_map.add_reg(this.PWRTMG, `UVM_REG_ADDR_WIDTH'hD0C, "RW", 0);
		this.PWRTMG_powerdown_to_x32 = this.PWRTMG.powerdown_to_x32;
		this.powerdown_to_x32 = this.PWRTMG.powerdown_to_x32;
		this.PWRTMG_selfref_to_x32 = this.PWRTMG.selfref_to_x32;
		this.selfref_to_x32 = this.PWRTMG.selfref_to_x32;
      this.DDR4PPRTMG0 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DDR4PPRTMG0::type_id::create("DDR4PPRTMG0",,get_full_name());
      if(this.DDR4PPRTMG0.has_coverage(UVM_CVR_REG_BITS))
      	this.DDR4PPRTMG0.cg_bits.option.name = {get_name(), ".", "DDR4PPRTMG0_bits"};
      this.DDR4PPRTMG0.configure(this, null, "");
      this.DDR4PPRTMG0.build();
	  uvm_resource_db#(string)::set({"REG::", DDR4PPRTMG0.get_full_name()}, "accessType", "NONSECURE", this);
         this.DDR4PPRTMG0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_pgm_x1_x1024", 0, 22},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_pgm_x1_sel", 31, 1}
         });
      this.default_map.add_reg(this.DDR4PPRTMG0, `UVM_REG_ADDR_WIDTH'hD30, "RW", 0);
		this.DDR4PPRTMG0_t_pgm_x1_x1024 = this.DDR4PPRTMG0.t_pgm_x1_x1024;
		this.t_pgm_x1_x1024 = this.DDR4PPRTMG0.t_pgm_x1_x1024;
		this.DDR4PPRTMG0_t_pgm_x1_sel = this.DDR4PPRTMG0.t_pgm_x1_sel;
		this.t_pgm_x1_sel = this.DDR4PPRTMG0.t_pgm_x1_sel;
      this.DDR4PPRTMG1 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_DDR4PPRTMG1::type_id::create("DDR4PPRTMG1",,get_full_name());
      if(this.DDR4PPRTMG1.has_coverage(UVM_CVR_REG_BITS))
      	this.DDR4PPRTMG1.cg_bits.option.name = {get_name(), ".", "DDR4PPRTMG1_bits"};
      this.DDR4PPRTMG1.configure(this, null, "");
      this.DDR4PPRTMG1.build();
	  uvm_resource_db#(string)::set({"REG::", DDR4PPRTMG1.get_full_name()}, "accessType", "NONSECURE", this);
         this.DDR4PPRTMG1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_pgmpst_x32", 0, 16},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_freq0_ch0_t_pgm_exit", 24, 6}
         });
      this.default_map.add_reg(this.DDR4PPRTMG1, `UVM_REG_ADDR_WIDTH'hD34, "RW", 0);
		this.DDR4PPRTMG1_t_pgmpst_x32 = this.DDR4PPRTMG1.t_pgmpst_x32;
		this.t_pgmpst_x32 = this.DDR4PPRTMG1.t_pgmpst_x32;
		this.DDR4PPRTMG1_t_pgm_exit = this.DDR4PPRTMG1.t_pgm_exit;
		this.t_pgm_exit = this.DDR4PPRTMG1.t_pgm_exit;
      this.LNKECCCTL0 = ral_reg_DWC_ddrctl_map_REGB_FREQ0_CH0_LNKECCCTL0::type_id::create("LNKECCCTL0",,get_full_name());
      if(this.LNKECCCTL0.has_coverage(UVM_CVR_REG_BITS))
      	this.LNKECCCTL0.cg_bits.option.name = {get_name(), ".", "LNKECCCTL0_bits"};
      this.LNKECCCTL0.configure(this, null, "");
      this.LNKECCCTL0.build();
	  uvm_resource_db#(string)::set({"REG::", LNKECCCTL0.get_full_name()}, "accessType", "NONSECURE", this);
         this.LNKECCCTL0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_wr_link_ecc_enable", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_freq0_ch0_rd_link_ecc_enable", 1, 1}
         });
      this.default_map.add_reg(this.LNKECCCTL0, `UVM_REG_ADDR_WIDTH'hD80, "RW", 0);
		this.LNKECCCTL0_wr_link_ecc_enable = this.LNKECCCTL0.wr_link_ecc_enable;
		this.wr_link_ecc_enable = this.LNKECCCTL0.wr_link_ecc_enable;
		this.LNKECCCTL0_rd_link_ecc_enable = this.LNKECCCTL0.rd_link_ecc_enable;
		this.rd_link_ecc_enable = this.LNKECCCTL0.rd_link_ecc_enable;
   endfunction : build

	`uvm_object_utils(ral_block_DWC_ddrctl_map_REGB_FREQ0_CH0)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_ddrctl_map_REGB_FREQ0_CH0


endpackage
`endif
