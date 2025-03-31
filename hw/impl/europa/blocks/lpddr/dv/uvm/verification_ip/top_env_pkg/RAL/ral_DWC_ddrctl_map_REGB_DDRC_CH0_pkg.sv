`ifndef RAL_DWC_DDRCTL_MAP_REGB_DDRC_CH0_PKG
`define RAL_DWC_DDRCTL_MAP_REGB_DDRC_CH0_PKG
package ral_DWC_ddrctl_map_REGB_DDRC_CH0_pkg;
import uvm_pkg::*;
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MSTR0 extends uvm_reg;
	rand uvm_reg_field lpddr4;
	rand uvm_reg_field lpddr5;
	rand uvm_reg_field lpddr5x;
	rand uvm_reg_field data_bus_width;
	rand uvm_reg_field burst_rdwr;
	rand uvm_reg_field active_ranks;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   lpddr4: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   lpddr5: coverpoint {m_data[3:3], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   lpddr5x: coverpoint {m_data[11:11], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   data_bus_width: coverpoint {m_data[13:12], m_is_read} iff(m_be) {
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
	   burst_rdwr: coverpoint {m_data[20:16], m_is_read} iff(m_be) {
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
	   active_ranks: coverpoint {m_data[25:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_MSTR0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.lpddr4 = uvm_reg_field::type_id::create("lpddr4",,get_full_name());
      this.lpddr4.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.lpddr5 = uvm_reg_field::type_id::create("lpddr5",,get_full_name());
      this.lpddr5.configure(this, 1, 3, "RW", 0, 1'h0, 1, 0, 0);
      this.lpddr5x = uvm_reg_field::type_id::create("lpddr5x",,get_full_name());
      this.lpddr5x.configure(this, 1, 11, "RW", 0, 1'h0, 1, 0, 0);
      this.data_bus_width = uvm_reg_field::type_id::create("data_bus_width",,get_full_name());
      this.data_bus_width.configure(this, 2, 12, "RW", 0, 2'h0, 1, 0, 0);
      this.burst_rdwr = uvm_reg_field::type_id::create("burst_rdwr",,get_full_name());
      this.burst_rdwr.configure(this, 5, 16, "RW", 0, 5'h4, 1, 0, 1);
      this.active_ranks = uvm_reg_field::type_id::create("active_ranks",,get_full_name());
      this.active_ranks.configure(this, 2, 24, "RW", 0, 2'h3, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MSTR0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MSTR0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MSTR2 extends uvm_reg;
	rand uvm_reg_field target_frequency;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   target_frequency: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_MSTR2");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.target_frequency = uvm_reg_field::type_id::create("target_frequency",,get_full_name());
      this.target_frequency.configure(this, 2, 0, "RW", 1, 2'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MSTR2)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MSTR2
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MSTR4 extends uvm_reg;
	rand uvm_reg_field wck_on;
	rand uvm_reg_field wck_suspend_en;
	rand uvm_reg_field ws_off_en;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   wck_on: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   wck_suspend_en: coverpoint {m_data[4:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ws_off_en: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_MSTR4");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.wck_on = uvm_reg_field::type_id::create("wck_on",,get_full_name());
      this.wck_on.configure(this, 1, 0, "RW", 1, 1'h0, 1, 0, 0);
      this.wck_suspend_en = uvm_reg_field::type_id::create("wck_suspend_en",,get_full_name());
      this.wck_suspend_en.configure(this, 1, 4, "RW", 1, 1'h0, 1, 0, 0);
      this.ws_off_en = uvm_reg_field::type_id::create("ws_off_en",,get_full_name());
      this.ws_off_en.configure(this, 1, 8, "RW", 1, 1'h1, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MSTR4)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MSTR4
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_STAT extends uvm_reg;
	uvm_reg_field operating_mode;
	uvm_reg_field selfref_type;
	uvm_reg_field selfref_state;
	uvm_reg_field selfref_cam_not_empty;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   operating_mode: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	   selfref_type: coverpoint {m_data[5:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {3'b?00};
	      wildcard bins bit_0_wr_as_1 = {3'b?10};
	      wildcard bins bit_0_rd = {3'b??1};
	      wildcard bins bit_1_wr_as_0 = {3'b0?0};
	      wildcard bins bit_1_wr_as_1 = {3'b1?0};
	      wildcard bins bit_1_rd = {3'b??1};
	      option.weight = 6;
	   }
	   selfref_state: coverpoint {m_data[14:12], m_is_read} iff(m_be) {
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
	   selfref_cam_not_empty: coverpoint {m_data[16:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_STAT");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.operating_mode = uvm_reg_field::type_id::create("operating_mode",,get_full_name());
      this.operating_mode.configure(this, 3, 0, "RO", 0, 3'h0, 1, 0, 0);
      this.selfref_type = uvm_reg_field::type_id::create("selfref_type",,get_full_name());
      this.selfref_type.configure(this, 2, 4, "RO", 0, 2'h0, 1, 0, 0);
      this.selfref_state = uvm_reg_field::type_id::create("selfref_state",,get_full_name());
      this.selfref_state.configure(this, 3, 12, "RO", 0, 3'h0, 1, 0, 1);
      this.selfref_cam_not_empty = uvm_reg_field::type_id::create("selfref_cam_not_empty",,get_full_name());
      this.selfref_cam_not_empty.configure(this, 1, 16, "RO", 0, 1'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_STAT)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_STAT
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRCTRL0 extends uvm_reg;
	rand uvm_reg_field mr_type;
	rand uvm_reg_field sw_init_int;
	rand uvm_reg_field mr_rank;
	rand uvm_reg_field mr_addr;
	rand uvm_reg_field mrr_done_clr;
	rand uvm_reg_field dis_mrrw_trfc;
	rand uvm_reg_field ppr_en;
	rand uvm_reg_field ppr_pgmpst_en;
	rand uvm_reg_field mr_wr;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   mr_type: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   sw_init_int: coverpoint {m_data[3:3], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   mr_rank: coverpoint {m_data[5:4], m_is_read} iff(m_be) {
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
	   mr_addr: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	   mrr_done_clr: coverpoint {m_data[24:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dis_mrrw_trfc: coverpoint {m_data[27:27], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ppr_en: coverpoint {m_data[28:28], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ppr_pgmpst_en: coverpoint {m_data[29:29], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   mr_wr: coverpoint {m_data[31:31], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_MRCTRL0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.mr_type = uvm_reg_field::type_id::create("mr_type",,get_full_name());
      this.mr_type.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.sw_init_int = uvm_reg_field::type_id::create("sw_init_int",,get_full_name());
      this.sw_init_int.configure(this, 1, 3, "RW", 0, 1'h0, 1, 0, 0);
      this.mr_rank = uvm_reg_field::type_id::create("mr_rank",,get_full_name());
      this.mr_rank.configure(this, 2, 4, "RW", 0, 2'h3, 1, 0, 0);
      this.mr_addr = uvm_reg_field::type_id::create("mr_addr",,get_full_name());
      this.mr_addr.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 1);
      this.mrr_done_clr = uvm_reg_field::type_id::create("mrr_done_clr",,get_full_name());
      this.mrr_done_clr.configure(this, 1, 24, "W1C", 0, 1'h0, 1, 0, 0);
      this.dis_mrrw_trfc = uvm_reg_field::type_id::create("dis_mrrw_trfc",,get_full_name());
      this.dis_mrrw_trfc.configure(this, 1, 27, "RW", 0, 1'h0, 1, 0, 0);
      this.ppr_en = uvm_reg_field::type_id::create("ppr_en",,get_full_name());
      this.ppr_en.configure(this, 1, 28, "RW", 0, 1'h0, 1, 0, 0);
      this.ppr_pgmpst_en = uvm_reg_field::type_id::create("ppr_pgmpst_en",,get_full_name());
      this.ppr_pgmpst_en.configure(this, 1, 29, "RW", 0, 1'h0, 1, 0, 0);
      this.mr_wr = uvm_reg_field::type_id::create("mr_wr",,get_full_name());
      this.mr_wr.configure(this, 1, 31, "W1S", 0, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRCTRL0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRCTRL0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRCTRL1 extends uvm_reg;
	rand uvm_reg_field mr_data;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   mr_data: coverpoint {m_data[17:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {19'b?????????????????00};
	      wildcard bins bit_0_wr_as_1 = {19'b?????????????????10};
	      wildcard bins bit_0_rd_as_0 = {19'b?????????????????01};
	      wildcard bins bit_0_rd_as_1 = {19'b?????????????????11};
	      wildcard bins bit_1_wr_as_0 = {19'b????????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {19'b????????????????1?0};
	      wildcard bins bit_1_rd_as_0 = {19'b????????????????0?1};
	      wildcard bins bit_1_rd_as_1 = {19'b????????????????1?1};
	      wildcard bins bit_2_wr_as_0 = {19'b???????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {19'b???????????????1??0};
	      wildcard bins bit_2_rd_as_0 = {19'b???????????????0??1};
	      wildcard bins bit_2_rd_as_1 = {19'b???????????????1??1};
	      wildcard bins bit_3_wr_as_0 = {19'b??????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {19'b??????????????1???0};
	      wildcard bins bit_3_rd_as_0 = {19'b??????????????0???1};
	      wildcard bins bit_3_rd_as_1 = {19'b??????????????1???1};
	      wildcard bins bit_4_wr_as_0 = {19'b?????????????0????0};
	      wildcard bins bit_4_wr_as_1 = {19'b?????????????1????0};
	      wildcard bins bit_4_rd_as_0 = {19'b?????????????0????1};
	      wildcard bins bit_4_rd_as_1 = {19'b?????????????1????1};
	      wildcard bins bit_5_wr_as_0 = {19'b????????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {19'b????????????1?????0};
	      wildcard bins bit_5_rd_as_0 = {19'b????????????0?????1};
	      wildcard bins bit_5_rd_as_1 = {19'b????????????1?????1};
	      wildcard bins bit_6_wr_as_0 = {19'b???????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {19'b???????????1??????0};
	      wildcard bins bit_6_rd_as_0 = {19'b???????????0??????1};
	      wildcard bins bit_6_rd_as_1 = {19'b???????????1??????1};
	      wildcard bins bit_7_wr_as_0 = {19'b??????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {19'b??????????1???????0};
	      wildcard bins bit_7_rd_as_0 = {19'b??????????0???????1};
	      wildcard bins bit_7_rd_as_1 = {19'b??????????1???????1};
	      wildcard bins bit_8_wr_as_0 = {19'b?????????0????????0};
	      wildcard bins bit_8_wr_as_1 = {19'b?????????1????????0};
	      wildcard bins bit_8_rd_as_0 = {19'b?????????0????????1};
	      wildcard bins bit_8_rd_as_1 = {19'b?????????1????????1};
	      wildcard bins bit_9_wr_as_0 = {19'b????????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {19'b????????1?????????0};
	      wildcard bins bit_9_rd_as_0 = {19'b????????0?????????1};
	      wildcard bins bit_9_rd_as_1 = {19'b????????1?????????1};
	      wildcard bins bit_10_wr_as_0 = {19'b???????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {19'b???????1??????????0};
	      wildcard bins bit_10_rd_as_0 = {19'b???????0??????????1};
	      wildcard bins bit_10_rd_as_1 = {19'b???????1??????????1};
	      wildcard bins bit_11_wr_as_0 = {19'b??????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {19'b??????1???????????0};
	      wildcard bins bit_11_rd_as_0 = {19'b??????0???????????1};
	      wildcard bins bit_11_rd_as_1 = {19'b??????1???????????1};
	      wildcard bins bit_12_wr_as_0 = {19'b?????0????????????0};
	      wildcard bins bit_12_wr_as_1 = {19'b?????1????????????0};
	      wildcard bins bit_12_rd_as_0 = {19'b?????0????????????1};
	      wildcard bins bit_12_rd_as_1 = {19'b?????1????????????1};
	      wildcard bins bit_13_wr_as_0 = {19'b????0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {19'b????1?????????????0};
	      wildcard bins bit_13_rd_as_0 = {19'b????0?????????????1};
	      wildcard bins bit_13_rd_as_1 = {19'b????1?????????????1};
	      wildcard bins bit_14_wr_as_0 = {19'b???0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {19'b???1??????????????0};
	      wildcard bins bit_14_rd_as_0 = {19'b???0??????????????1};
	      wildcard bins bit_14_rd_as_1 = {19'b???1??????????????1};
	      wildcard bins bit_15_wr_as_0 = {19'b??0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {19'b??1???????????????0};
	      wildcard bins bit_15_rd_as_0 = {19'b??0???????????????1};
	      wildcard bins bit_15_rd_as_1 = {19'b??1???????????????1};
	      wildcard bins bit_16_wr_as_0 = {19'b?0????????????????0};
	      wildcard bins bit_16_wr_as_1 = {19'b?1????????????????0};
	      wildcard bins bit_16_rd_as_0 = {19'b?0????????????????1};
	      wildcard bins bit_16_rd_as_1 = {19'b?1????????????????1};
	      wildcard bins bit_17_wr_as_0 = {19'b0?????????????????0};
	      wildcard bins bit_17_wr_as_1 = {19'b1?????????????????0};
	      wildcard bins bit_17_rd_as_0 = {19'b0?????????????????1};
	      wildcard bins bit_17_rd_as_1 = {19'b1?????????????????1};
	      option.weight = 72;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_MRCTRL1");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.mr_data = uvm_reg_field::type_id::create("mr_data",,get_full_name());
      this.mr_data.configure(this, 18, 0, "RW", 0, 18'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRCTRL1)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRCTRL1
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRSTAT extends uvm_reg;
	uvm_reg_field mr_wr_busy;
	uvm_reg_field mrr_done;
	uvm_reg_field ppr_done;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   mr_wr_busy: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   mrr_done: coverpoint {m_data[16:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   ppr_done: coverpoint {m_data[17:17], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_MRSTAT");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.mr_wr_busy = uvm_reg_field::type_id::create("mr_wr_busy",,get_full_name());
      this.mr_wr_busy.configure(this, 1, 0, "RO", 0, 1'h0, 1, 0, 1);
      this.mrr_done = uvm_reg_field::type_id::create("mrr_done",,get_full_name());
      this.mrr_done.configure(this, 1, 16, "RO", 0, 1'h0, 1, 0, 0);
      this.ppr_done = uvm_reg_field::type_id::create("ppr_done",,get_full_name());
      this.ppr_done.configure(this, 1, 17, "RO", 0, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRSTAT)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRSTAT
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRRDATA0 extends uvm_reg;
	uvm_reg_field mrr_data_lwr;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   mrr_data_lwr: coverpoint {m_data[31:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {33'b???????????????????????????????00};
	      wildcard bins bit_0_wr_as_1 = {33'b???????????????????????????????10};
	      wildcard bins bit_0_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_1_wr_as_0 = {33'b??????????????????????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {33'b??????????????????????????????1?0};
	      wildcard bins bit_1_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_2_wr_as_0 = {33'b?????????????????????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {33'b?????????????????????????????1??0};
	      wildcard bins bit_2_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_3_wr_as_0 = {33'b????????????????????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {33'b????????????????????????????1???0};
	      wildcard bins bit_3_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_4_wr_as_0 = {33'b???????????????????????????0????0};
	      wildcard bins bit_4_wr_as_1 = {33'b???????????????????????????1????0};
	      wildcard bins bit_4_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_5_wr_as_0 = {33'b??????????????????????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {33'b??????????????????????????1?????0};
	      wildcard bins bit_5_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_6_wr_as_0 = {33'b?????????????????????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {33'b?????????????????????????1??????0};
	      wildcard bins bit_6_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_7_wr_as_0 = {33'b????????????????????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {33'b????????????????????????1???????0};
	      wildcard bins bit_7_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_8_wr_as_0 = {33'b???????????????????????0????????0};
	      wildcard bins bit_8_wr_as_1 = {33'b???????????????????????1????????0};
	      wildcard bins bit_8_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_9_wr_as_0 = {33'b??????????????????????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {33'b??????????????????????1?????????0};
	      wildcard bins bit_9_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_10_wr_as_0 = {33'b?????????????????????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {33'b?????????????????????1??????????0};
	      wildcard bins bit_10_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_11_wr_as_0 = {33'b????????????????????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {33'b????????????????????1???????????0};
	      wildcard bins bit_11_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_12_wr_as_0 = {33'b???????????????????0????????????0};
	      wildcard bins bit_12_wr_as_1 = {33'b???????????????????1????????????0};
	      wildcard bins bit_12_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_13_wr_as_0 = {33'b??????????????????0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {33'b??????????????????1?????????????0};
	      wildcard bins bit_13_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_14_wr_as_0 = {33'b?????????????????0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {33'b?????????????????1??????????????0};
	      wildcard bins bit_14_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_15_wr_as_0 = {33'b????????????????0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {33'b????????????????1???????????????0};
	      wildcard bins bit_15_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_16_wr_as_0 = {33'b???????????????0????????????????0};
	      wildcard bins bit_16_wr_as_1 = {33'b???????????????1????????????????0};
	      wildcard bins bit_16_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_17_wr_as_0 = {33'b??????????????0?????????????????0};
	      wildcard bins bit_17_wr_as_1 = {33'b??????????????1?????????????????0};
	      wildcard bins bit_17_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_18_wr_as_0 = {33'b?????????????0??????????????????0};
	      wildcard bins bit_18_wr_as_1 = {33'b?????????????1??????????????????0};
	      wildcard bins bit_18_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_19_wr_as_0 = {33'b????????????0???????????????????0};
	      wildcard bins bit_19_wr_as_1 = {33'b????????????1???????????????????0};
	      wildcard bins bit_19_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_20_wr_as_0 = {33'b???????????0????????????????????0};
	      wildcard bins bit_20_wr_as_1 = {33'b???????????1????????????????????0};
	      wildcard bins bit_20_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_21_wr_as_0 = {33'b??????????0?????????????????????0};
	      wildcard bins bit_21_wr_as_1 = {33'b??????????1?????????????????????0};
	      wildcard bins bit_21_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_22_wr_as_0 = {33'b?????????0??????????????????????0};
	      wildcard bins bit_22_wr_as_1 = {33'b?????????1??????????????????????0};
	      wildcard bins bit_22_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_23_wr_as_0 = {33'b????????0???????????????????????0};
	      wildcard bins bit_23_wr_as_1 = {33'b????????1???????????????????????0};
	      wildcard bins bit_23_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_24_wr_as_0 = {33'b???????0????????????????????????0};
	      wildcard bins bit_24_wr_as_1 = {33'b???????1????????????????????????0};
	      wildcard bins bit_24_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_25_wr_as_0 = {33'b??????0?????????????????????????0};
	      wildcard bins bit_25_wr_as_1 = {33'b??????1?????????????????????????0};
	      wildcard bins bit_25_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_26_wr_as_0 = {33'b?????0??????????????????????????0};
	      wildcard bins bit_26_wr_as_1 = {33'b?????1??????????????????????????0};
	      wildcard bins bit_26_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_27_wr_as_0 = {33'b????0???????????????????????????0};
	      wildcard bins bit_27_wr_as_1 = {33'b????1???????????????????????????0};
	      wildcard bins bit_27_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_28_wr_as_0 = {33'b???0????????????????????????????0};
	      wildcard bins bit_28_wr_as_1 = {33'b???1????????????????????????????0};
	      wildcard bins bit_28_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_29_wr_as_0 = {33'b??0?????????????????????????????0};
	      wildcard bins bit_29_wr_as_1 = {33'b??1?????????????????????????????0};
	      wildcard bins bit_29_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_30_wr_as_0 = {33'b?0??????????????????????????????0};
	      wildcard bins bit_30_wr_as_1 = {33'b?1??????????????????????????????0};
	      wildcard bins bit_30_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_31_wr_as_0 = {33'b0???????????????????????????????0};
	      wildcard bins bit_31_wr_as_1 = {33'b1???????????????????????????????0};
	      wildcard bins bit_31_rd = {33'b????????????????????????????????1};
	      option.weight = 96;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_MRRDATA0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.mrr_data_lwr = uvm_reg_field::type_id::create("mrr_data_lwr",,get_full_name());
      this.mrr_data_lwr.configure(this, 32, 0, "RO", 0, 32'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRRDATA0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRRDATA0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRRDATA1 extends uvm_reg;
	uvm_reg_field mrr_data_upr;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   mrr_data_upr: coverpoint {m_data[31:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {33'b???????????????????????????????00};
	      wildcard bins bit_0_wr_as_1 = {33'b???????????????????????????????10};
	      wildcard bins bit_0_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_1_wr_as_0 = {33'b??????????????????????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {33'b??????????????????????????????1?0};
	      wildcard bins bit_1_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_2_wr_as_0 = {33'b?????????????????????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {33'b?????????????????????????????1??0};
	      wildcard bins bit_2_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_3_wr_as_0 = {33'b????????????????????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {33'b????????????????????????????1???0};
	      wildcard bins bit_3_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_4_wr_as_0 = {33'b???????????????????????????0????0};
	      wildcard bins bit_4_wr_as_1 = {33'b???????????????????????????1????0};
	      wildcard bins bit_4_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_5_wr_as_0 = {33'b??????????????????????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {33'b??????????????????????????1?????0};
	      wildcard bins bit_5_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_6_wr_as_0 = {33'b?????????????????????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {33'b?????????????????????????1??????0};
	      wildcard bins bit_6_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_7_wr_as_0 = {33'b????????????????????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {33'b????????????????????????1???????0};
	      wildcard bins bit_7_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_8_wr_as_0 = {33'b???????????????????????0????????0};
	      wildcard bins bit_8_wr_as_1 = {33'b???????????????????????1????????0};
	      wildcard bins bit_8_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_9_wr_as_0 = {33'b??????????????????????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {33'b??????????????????????1?????????0};
	      wildcard bins bit_9_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_10_wr_as_0 = {33'b?????????????????????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {33'b?????????????????????1??????????0};
	      wildcard bins bit_10_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_11_wr_as_0 = {33'b????????????????????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {33'b????????????????????1???????????0};
	      wildcard bins bit_11_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_12_wr_as_0 = {33'b???????????????????0????????????0};
	      wildcard bins bit_12_wr_as_1 = {33'b???????????????????1????????????0};
	      wildcard bins bit_12_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_13_wr_as_0 = {33'b??????????????????0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {33'b??????????????????1?????????????0};
	      wildcard bins bit_13_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_14_wr_as_0 = {33'b?????????????????0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {33'b?????????????????1??????????????0};
	      wildcard bins bit_14_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_15_wr_as_0 = {33'b????????????????0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {33'b????????????????1???????????????0};
	      wildcard bins bit_15_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_16_wr_as_0 = {33'b???????????????0????????????????0};
	      wildcard bins bit_16_wr_as_1 = {33'b???????????????1????????????????0};
	      wildcard bins bit_16_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_17_wr_as_0 = {33'b??????????????0?????????????????0};
	      wildcard bins bit_17_wr_as_1 = {33'b??????????????1?????????????????0};
	      wildcard bins bit_17_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_18_wr_as_0 = {33'b?????????????0??????????????????0};
	      wildcard bins bit_18_wr_as_1 = {33'b?????????????1??????????????????0};
	      wildcard bins bit_18_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_19_wr_as_0 = {33'b????????????0???????????????????0};
	      wildcard bins bit_19_wr_as_1 = {33'b????????????1???????????????????0};
	      wildcard bins bit_19_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_20_wr_as_0 = {33'b???????????0????????????????????0};
	      wildcard bins bit_20_wr_as_1 = {33'b???????????1????????????????????0};
	      wildcard bins bit_20_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_21_wr_as_0 = {33'b??????????0?????????????????????0};
	      wildcard bins bit_21_wr_as_1 = {33'b??????????1?????????????????????0};
	      wildcard bins bit_21_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_22_wr_as_0 = {33'b?????????0??????????????????????0};
	      wildcard bins bit_22_wr_as_1 = {33'b?????????1??????????????????????0};
	      wildcard bins bit_22_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_23_wr_as_0 = {33'b????????0???????????????????????0};
	      wildcard bins bit_23_wr_as_1 = {33'b????????1???????????????????????0};
	      wildcard bins bit_23_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_24_wr_as_0 = {33'b???????0????????????????????????0};
	      wildcard bins bit_24_wr_as_1 = {33'b???????1????????????????????????0};
	      wildcard bins bit_24_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_25_wr_as_0 = {33'b??????0?????????????????????????0};
	      wildcard bins bit_25_wr_as_1 = {33'b??????1?????????????????????????0};
	      wildcard bins bit_25_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_26_wr_as_0 = {33'b?????0??????????????????????????0};
	      wildcard bins bit_26_wr_as_1 = {33'b?????1??????????????????????????0};
	      wildcard bins bit_26_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_27_wr_as_0 = {33'b????0???????????????????????????0};
	      wildcard bins bit_27_wr_as_1 = {33'b????1???????????????????????????0};
	      wildcard bins bit_27_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_28_wr_as_0 = {33'b???0????????????????????????????0};
	      wildcard bins bit_28_wr_as_1 = {33'b???1????????????????????????????0};
	      wildcard bins bit_28_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_29_wr_as_0 = {33'b??0?????????????????????????????0};
	      wildcard bins bit_29_wr_as_1 = {33'b??1?????????????????????????????0};
	      wildcard bins bit_29_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_30_wr_as_0 = {33'b?0??????????????????????????????0};
	      wildcard bins bit_30_wr_as_1 = {33'b?1??????????????????????????????0};
	      wildcard bins bit_30_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_31_wr_as_0 = {33'b0???????????????????????????????0};
	      wildcard bins bit_31_wr_as_1 = {33'b1???????????????????????????????0};
	      wildcard bins bit_31_rd = {33'b????????????????????????????????1};
	      option.weight = 96;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_MRRDATA1");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.mrr_data_upr = uvm_reg_field::type_id::create("mrr_data_upr",,get_full_name());
      this.mrr_data_upr.configure(this, 32, 0, "RO", 0, 32'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRRDATA1)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRRDATA1
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL0 extends uvm_reg;
	rand uvm_reg_field derate_enable;
	rand uvm_reg_field lpddr4_refresh_mode;
	rand uvm_reg_field derate_mr4_pause_fc;
	rand uvm_reg_field dis_trefi_x6x8;
	rand uvm_reg_field dis_trefi_x0125;
	rand uvm_reg_field use_slow_rm_in_low_temp;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   derate_enable: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   lpddr4_refresh_mode: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   derate_mr4_pause_fc: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dis_trefi_x6x8: coverpoint {m_data[3:3], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dis_trefi_x0125: coverpoint {m_data[4:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   use_slow_rm_in_low_temp: coverpoint {m_data[5:5], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL0");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.derate_enable = uvm_reg_field::type_id::create("derate_enable",,get_full_name());
      this.derate_enable.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.lpddr4_refresh_mode = uvm_reg_field::type_id::create("lpddr4_refresh_mode",,get_full_name());
      this.lpddr4_refresh_mode.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.derate_mr4_pause_fc = uvm_reg_field::type_id::create("derate_mr4_pause_fc",,get_full_name());
      this.derate_mr4_pause_fc.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
      this.dis_trefi_x6x8 = uvm_reg_field::type_id::create("dis_trefi_x6x8",,get_full_name());
      this.dis_trefi_x6x8.configure(this, 1, 3, "RW", 0, 1'h0, 1, 0, 0);
      this.dis_trefi_x0125 = uvm_reg_field::type_id::create("dis_trefi_x0125",,get_full_name());
      this.dis_trefi_x0125.configure(this, 1, 4, "RW", 0, 1'h0, 1, 0, 0);
      this.use_slow_rm_in_low_temp = uvm_reg_field::type_id::create("use_slow_rm_in_low_temp",,get_full_name());
      this.use_slow_rm_in_low_temp.configure(this, 1, 5, "RW", 0, 1'h1, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL1 extends uvm_reg;
	rand uvm_reg_field active_derate_byte_rank0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   active_derate_byte_rank0: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL1");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.active_derate_byte_rank0 = uvm_reg_field::type_id::create("active_derate_byte_rank0",,get_full_name());
      this.active_derate_byte_rank0.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL1)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL1
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL2 extends uvm_reg;
	rand uvm_reg_field active_derate_byte_rank1;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   active_derate_byte_rank1: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL2");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.active_derate_byte_rank1 = uvm_reg_field::type_id::create("active_derate_byte_rank1",,get_full_name());
      this.active_derate_byte_rank1.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL2)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL2
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL5 extends uvm_reg;
	rand uvm_reg_field derate_temp_limit_intr_en;
	rand uvm_reg_field derate_temp_limit_intr_clr;
	rand uvm_reg_field derate_temp_limit_intr_force;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   derate_temp_limit_intr_en: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   derate_temp_limit_intr_clr: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   derate_temp_limit_intr_force: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL5");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.derate_temp_limit_intr_en = uvm_reg_field::type_id::create("derate_temp_limit_intr_en",,get_full_name());
      this.derate_temp_limit_intr_en.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 0);
      this.derate_temp_limit_intr_clr = uvm_reg_field::type_id::create("derate_temp_limit_intr_clr",,get_full_name());
      this.derate_temp_limit_intr_clr.configure(this, 1, 1, "W1C", 0, 1'h0, 1, 0, 0);
      this.derate_temp_limit_intr_force = uvm_reg_field::type_id::create("derate_temp_limit_intr_force",,get_full_name());
      this.derate_temp_limit_intr_force.configure(this, 1, 2, "W1C", 0, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL5)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL5
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL6 extends uvm_reg;
	rand uvm_reg_field derate_mr4_tuf_dis;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   derate_mr4_tuf_dis: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL6");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.derate_mr4_tuf_dis = uvm_reg_field::type_id::create("derate_mr4_tuf_dis",,get_full_name());
      this.derate_mr4_tuf_dis.configure(this, 1, 0, "RW", 1, 1'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL6)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL6
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATESTAT0 extends uvm_reg;
	uvm_reg_field derate_temp_limit_intr;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   derate_temp_limit_intr: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_DERATESTAT0");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.derate_temp_limit_intr = uvm_reg_field::type_id::create("derate_temp_limit_intr",,get_full_name());
      this.derate_temp_limit_intr.configure(this, 1, 0, "RO", 0, 1'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATESTAT0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATESTAT0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATEDBGCTL extends uvm_reg;
	rand uvm_reg_field dbg_mr4_rank_sel;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dbg_mr4_rank_sel: coverpoint {m_data[5:4], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_DERATEDBGCTL");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dbg_mr4_rank_sel = uvm_reg_field::type_id::create("dbg_mr4_rank_sel",,get_full_name());
      this.dbg_mr4_rank_sel.configure(this, 2, 4, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATEDBGCTL)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATEDBGCTL
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATEDBGSTAT extends uvm_reg;
	uvm_reg_field dbg_mr4_byte0;
	uvm_reg_field dbg_mr4_byte1;
	uvm_reg_field dbg_mr4_byte2;
	uvm_reg_field dbg_mr4_byte3;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dbg_mr4_byte0: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {9'b???????00};
	      wildcard bins bit_0_wr_as_1 = {9'b???????10};
	      wildcard bins bit_0_rd = {9'b????????1};
	      wildcard bins bit_1_wr_as_0 = {9'b??????0?0};
	      wildcard bins bit_1_wr_as_1 = {9'b??????1?0};
	      wildcard bins bit_1_rd = {9'b????????1};
	      wildcard bins bit_2_wr_as_0 = {9'b?????0??0};
	      wildcard bins bit_2_wr_as_1 = {9'b?????1??0};
	      wildcard bins bit_2_rd = {9'b????????1};
	      wildcard bins bit_3_wr_as_0 = {9'b????0???0};
	      wildcard bins bit_3_wr_as_1 = {9'b????1???0};
	      wildcard bins bit_3_rd = {9'b????????1};
	      wildcard bins bit_4_wr_as_0 = {9'b???0????0};
	      wildcard bins bit_4_wr_as_1 = {9'b???1????0};
	      wildcard bins bit_4_rd = {9'b????????1};
	      wildcard bins bit_5_wr_as_0 = {9'b??0?????0};
	      wildcard bins bit_5_wr_as_1 = {9'b??1?????0};
	      wildcard bins bit_5_rd = {9'b????????1};
	      wildcard bins bit_6_wr_as_0 = {9'b?0??????0};
	      wildcard bins bit_6_wr_as_1 = {9'b?1??????0};
	      wildcard bins bit_6_rd = {9'b????????1};
	      wildcard bins bit_7_wr_as_0 = {9'b0???????0};
	      wildcard bins bit_7_wr_as_1 = {9'b1???????0};
	      wildcard bins bit_7_rd = {9'b????????1};
	      option.weight = 24;
	   }
	   dbg_mr4_byte1: coverpoint {m_data[15:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {9'b???????00};
	      wildcard bins bit_0_wr_as_1 = {9'b???????10};
	      wildcard bins bit_0_rd = {9'b????????1};
	      wildcard bins bit_1_wr_as_0 = {9'b??????0?0};
	      wildcard bins bit_1_wr_as_1 = {9'b??????1?0};
	      wildcard bins bit_1_rd = {9'b????????1};
	      wildcard bins bit_2_wr_as_0 = {9'b?????0??0};
	      wildcard bins bit_2_wr_as_1 = {9'b?????1??0};
	      wildcard bins bit_2_rd = {9'b????????1};
	      wildcard bins bit_3_wr_as_0 = {9'b????0???0};
	      wildcard bins bit_3_wr_as_1 = {9'b????1???0};
	      wildcard bins bit_3_rd = {9'b????????1};
	      wildcard bins bit_4_wr_as_0 = {9'b???0????0};
	      wildcard bins bit_4_wr_as_1 = {9'b???1????0};
	      wildcard bins bit_4_rd = {9'b????????1};
	      wildcard bins bit_5_wr_as_0 = {9'b??0?????0};
	      wildcard bins bit_5_wr_as_1 = {9'b??1?????0};
	      wildcard bins bit_5_rd = {9'b????????1};
	      wildcard bins bit_6_wr_as_0 = {9'b?0??????0};
	      wildcard bins bit_6_wr_as_1 = {9'b?1??????0};
	      wildcard bins bit_6_rd = {9'b????????1};
	      wildcard bins bit_7_wr_as_0 = {9'b0???????0};
	      wildcard bins bit_7_wr_as_1 = {9'b1???????0};
	      wildcard bins bit_7_rd = {9'b????????1};
	      option.weight = 24;
	   }
	   dbg_mr4_byte2: coverpoint {m_data[23:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {9'b???????00};
	      wildcard bins bit_0_wr_as_1 = {9'b???????10};
	      wildcard bins bit_0_rd = {9'b????????1};
	      wildcard bins bit_1_wr_as_0 = {9'b??????0?0};
	      wildcard bins bit_1_wr_as_1 = {9'b??????1?0};
	      wildcard bins bit_1_rd = {9'b????????1};
	      wildcard bins bit_2_wr_as_0 = {9'b?????0??0};
	      wildcard bins bit_2_wr_as_1 = {9'b?????1??0};
	      wildcard bins bit_2_rd = {9'b????????1};
	      wildcard bins bit_3_wr_as_0 = {9'b????0???0};
	      wildcard bins bit_3_wr_as_1 = {9'b????1???0};
	      wildcard bins bit_3_rd = {9'b????????1};
	      wildcard bins bit_4_wr_as_0 = {9'b???0????0};
	      wildcard bins bit_4_wr_as_1 = {9'b???1????0};
	      wildcard bins bit_4_rd = {9'b????????1};
	      wildcard bins bit_5_wr_as_0 = {9'b??0?????0};
	      wildcard bins bit_5_wr_as_1 = {9'b??1?????0};
	      wildcard bins bit_5_rd = {9'b????????1};
	      wildcard bins bit_6_wr_as_0 = {9'b?0??????0};
	      wildcard bins bit_6_wr_as_1 = {9'b?1??????0};
	      wildcard bins bit_6_rd = {9'b????????1};
	      wildcard bins bit_7_wr_as_0 = {9'b0???????0};
	      wildcard bins bit_7_wr_as_1 = {9'b1???????0};
	      wildcard bins bit_7_rd = {9'b????????1};
	      option.weight = 24;
	   }
	   dbg_mr4_byte3: coverpoint {m_data[31:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {9'b???????00};
	      wildcard bins bit_0_wr_as_1 = {9'b???????10};
	      wildcard bins bit_0_rd = {9'b????????1};
	      wildcard bins bit_1_wr_as_0 = {9'b??????0?0};
	      wildcard bins bit_1_wr_as_1 = {9'b??????1?0};
	      wildcard bins bit_1_rd = {9'b????????1};
	      wildcard bins bit_2_wr_as_0 = {9'b?????0??0};
	      wildcard bins bit_2_wr_as_1 = {9'b?????1??0};
	      wildcard bins bit_2_rd = {9'b????????1};
	      wildcard bins bit_3_wr_as_0 = {9'b????0???0};
	      wildcard bins bit_3_wr_as_1 = {9'b????1???0};
	      wildcard bins bit_3_rd = {9'b????????1};
	      wildcard bins bit_4_wr_as_0 = {9'b???0????0};
	      wildcard bins bit_4_wr_as_1 = {9'b???1????0};
	      wildcard bins bit_4_rd = {9'b????????1};
	      wildcard bins bit_5_wr_as_0 = {9'b??0?????0};
	      wildcard bins bit_5_wr_as_1 = {9'b??1?????0};
	      wildcard bins bit_5_rd = {9'b????????1};
	      wildcard bins bit_6_wr_as_0 = {9'b?0??????0};
	      wildcard bins bit_6_wr_as_1 = {9'b?1??????0};
	      wildcard bins bit_6_rd = {9'b????????1};
	      wildcard bins bit_7_wr_as_0 = {9'b0???????0};
	      wildcard bins bit_7_wr_as_1 = {9'b1???????0};
	      wildcard bins bit_7_rd = {9'b????????1};
	      option.weight = 24;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_DERATEDBGSTAT");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dbg_mr4_byte0 = uvm_reg_field::type_id::create("dbg_mr4_byte0",,get_full_name());
      this.dbg_mr4_byte0.configure(this, 8, 0, "RO", 0, 8'h0, 1, 0, 1);
      this.dbg_mr4_byte1 = uvm_reg_field::type_id::create("dbg_mr4_byte1",,get_full_name());
      this.dbg_mr4_byte1.configure(this, 8, 8, "RO", 0, 8'h0, 1, 0, 1);
      this.dbg_mr4_byte2 = uvm_reg_field::type_id::create("dbg_mr4_byte2",,get_full_name());
      this.dbg_mr4_byte2.configure(this, 8, 16, "RO", 0, 8'h0, 1, 0, 1);
      this.dbg_mr4_byte3 = uvm_reg_field::type_id::create("dbg_mr4_byte3",,get_full_name());
      this.dbg_mr4_byte3.configure(this, 8, 24, "RO", 0, 8'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATEDBGSTAT)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATEDBGSTAT
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_PWRCTL extends uvm_reg;
	rand uvm_reg_field selfref_en;
	rand uvm_reg_field powerdown_en;
	rand uvm_reg_field en_dfi_dram_clk_disable;
	rand uvm_reg_field selfref_sw;
	rand uvm_reg_field stay_in_selfref;
	rand uvm_reg_field dis_cam_drain_selfref;
	rand uvm_reg_field lpddr4_sr_allowed;
	rand uvm_reg_field dsm_en;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   selfref_en: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   powerdown_en: coverpoint {m_data[4:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   en_dfi_dram_clk_disable: coverpoint {m_data[9:9], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   selfref_sw: coverpoint {m_data[11:11], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   stay_in_selfref: coverpoint {m_data[15:15], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dis_cam_drain_selfref: coverpoint {m_data[16:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   lpddr4_sr_allowed: coverpoint {m_data[17:17], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dsm_en: coverpoint {m_data[18:18], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_PWRCTL");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.selfref_en = uvm_reg_field::type_id::create("selfref_en",,get_full_name());
      this.selfref_en.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.powerdown_en = uvm_reg_field::type_id::create("powerdown_en",,get_full_name());
      this.powerdown_en.configure(this, 1, 4, "RW", 0, 1'h0, 1, 0, 0);
      this.en_dfi_dram_clk_disable = uvm_reg_field::type_id::create("en_dfi_dram_clk_disable",,get_full_name());
      this.en_dfi_dram_clk_disable.configure(this, 1, 9, "RW", 0, 1'h0, 1, 0, 0);
      this.selfref_sw = uvm_reg_field::type_id::create("selfref_sw",,get_full_name());
      this.selfref_sw.configure(this, 1, 11, "RW", 0, 1'h0, 1, 0, 0);
      this.stay_in_selfref = uvm_reg_field::type_id::create("stay_in_selfref",,get_full_name());
      this.stay_in_selfref.configure(this, 1, 15, "RW", 0, 1'h0, 1, 0, 0);
      this.dis_cam_drain_selfref = uvm_reg_field::type_id::create("dis_cam_drain_selfref",,get_full_name());
      this.dis_cam_drain_selfref.configure(this, 1, 16, "RW", 0, 1'h0, 1, 0, 0);
      this.lpddr4_sr_allowed = uvm_reg_field::type_id::create("lpddr4_sr_allowed",,get_full_name());
      this.lpddr4_sr_allowed.configure(this, 1, 17, "RW", 0, 1'h0, 1, 0, 0);
      this.dsm_en = uvm_reg_field::type_id::create("dsm_en",,get_full_name());
      this.dsm_en.configure(this, 1, 18, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_PWRCTL)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_PWRCTL
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_HWLPCTL extends uvm_reg;
	rand uvm_reg_field hw_lp_en;
	rand uvm_reg_field hw_lp_exit_idle_en;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   hw_lp_en: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   hw_lp_exit_idle_en: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_HWLPCTL");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.hw_lp_en = uvm_reg_field::type_id::create("hw_lp_en",,get_full_name());
      this.hw_lp_en.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 0);
      this.hw_lp_exit_idle_en = uvm_reg_field::type_id::create("hw_lp_exit_idle_en",,get_full_name());
      this.hw_lp_exit_idle_en.configure(this, 1, 1, "RW", 0, 1'h1, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_HWLPCTL)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_HWLPCTL
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_CLKGATECTL extends uvm_reg;
	rand uvm_reg_field bsm_clk_on;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   bsm_clk_on: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_CLKGATECTL");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.bsm_clk_on = uvm_reg_field::type_id::create("bsm_clk_on",,get_full_name());
      this.bsm_clk_on.configure(this, 6, 0, "RW", 0, 6'h3f, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_CLKGATECTL)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_CLKGATECTL
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFSHMOD0 extends uvm_reg;
	rand uvm_reg_field refresh_burst;
	rand uvm_reg_field auto_refab_en;
	rand uvm_reg_field per_bank_refresh;
	rand uvm_reg_field per_bank_refresh_opt_en;
	rand uvm_reg_field fixed_crit_refpb_bank_en;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   refresh_burst: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
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
	   auto_refab_en: coverpoint {m_data[7:6], m_is_read} iff(m_be) {
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
	   per_bank_refresh: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   per_bank_refresh_opt_en: coverpoint {m_data[9:9], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   fixed_crit_refpb_bank_en: coverpoint {m_data[24:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_RFSHMOD0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.refresh_burst = uvm_reg_field::type_id::create("refresh_burst",,get_full_name());
      this.refresh_burst.configure(this, 6, 0, "RW", 0, 6'h0, 1, 0, 0);
      this.auto_refab_en = uvm_reg_field::type_id::create("auto_refab_en",,get_full_name());
      this.auto_refab_en.configure(this, 2, 6, "RW", 0, 2'h0, 1, 0, 0);
      this.per_bank_refresh = uvm_reg_field::type_id::create("per_bank_refresh",,get_full_name());
      this.per_bank_refresh.configure(this, 1, 8, "RW", 0, 1'h0, 1, 0, 0);
      this.per_bank_refresh_opt_en = uvm_reg_field::type_id::create("per_bank_refresh_opt_en",,get_full_name());
      this.per_bank_refresh_opt_en.configure(this, 1, 9, "RW", 0, 1'h0, 1, 0, 0);
      this.fixed_crit_refpb_bank_en = uvm_reg_field::type_id::create("fixed_crit_refpb_bank_en",,get_full_name());
      this.fixed_crit_refpb_bank_en.configure(this, 1, 24, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFSHMOD0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFSHMOD0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFSHCTL0 extends uvm_reg;
	rand uvm_reg_field dis_auto_refresh;
	rand uvm_reg_field refresh_update_level;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dis_auto_refresh: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   refresh_update_level: coverpoint {m_data[4:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_RFSHCTL0");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dis_auto_refresh = uvm_reg_field::type_id::create("dis_auto_refresh",,get_full_name());
      this.dis_auto_refresh.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.refresh_update_level = uvm_reg_field::type_id::create("refresh_update_level",,get_full_name());
      this.refresh_update_level.configure(this, 1, 4, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFSHCTL0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFSHCTL0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFMMOD0 extends uvm_reg;
	rand uvm_reg_field rfm_en;
	rand uvm_reg_field rfmsbc;
	rand uvm_reg_field raaimt;
	rand uvm_reg_field raamult;
	rand uvm_reg_field raadec;
	rand uvm_reg_field rfmth_rm_thr;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   rfm_en: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   rfmsbc: coverpoint {m_data[4:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   raaimt: coverpoint {m_data[12:8], m_is_read} iff(m_be) {
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
	   raamult: coverpoint {m_data[17:16], m_is_read} iff(m_be) {
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
	   raadec: coverpoint {m_data[19:18], m_is_read} iff(m_be) {
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
	   rfmth_rm_thr: coverpoint {m_data[28:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_RFMMOD0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.rfm_en = uvm_reg_field::type_id::create("rfm_en",,get_full_name());
      this.rfm_en.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.rfmsbc = uvm_reg_field::type_id::create("rfmsbc",,get_full_name());
      this.rfmsbc.configure(this, 1, 4, "RW", 0, 1'h0, 1, 0, 0);
      this.raaimt = uvm_reg_field::type_id::create("raaimt",,get_full_name());
      this.raaimt.configure(this, 5, 8, "RW", 0, 5'h1, 1, 0, 1);
      this.raamult = uvm_reg_field::type_id::create("raamult",,get_full_name());
      this.raamult.configure(this, 2, 16, "RW", 0, 2'h0, 1, 0, 0);
      this.raadec = uvm_reg_field::type_id::create("raadec",,get_full_name());
      this.raadec.configure(this, 2, 18, "RW", 0, 2'h0, 1, 0, 0);
      this.rfmth_rm_thr = uvm_reg_field::type_id::create("rfmth_rm_thr",,get_full_name());
      this.rfmth_rm_thr.configure(this, 5, 24, "RW", 0, 5'ha, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFMMOD0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFMMOD0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFMMOD1 extends uvm_reg;
	rand uvm_reg_field init_raa_cnt;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   init_raa_cnt: coverpoint {m_data[10:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_RFMMOD1");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.init_raa_cnt = uvm_reg_field::type_id::create("init_raa_cnt",,get_full_name());
      this.init_raa_cnt.configure(this, 11, 0, "RW", 0, 11'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFMMOD1)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFMMOD1
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFMCTL extends uvm_reg;
	rand uvm_reg_field dbg_raa_rank;
	rand uvm_reg_field dbg_raa_bg_bank;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dbg_raa_rank: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dbg_raa_bg_bank: coverpoint {m_data[7:4], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_RFMCTL");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dbg_raa_rank = uvm_reg_field::type_id::create("dbg_raa_rank",,get_full_name());
      this.dbg_raa_rank.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.dbg_raa_bg_bank = uvm_reg_field::type_id::create("dbg_raa_bg_bank",,get_full_name());
      this.dbg_raa_bg_bank.configure(this, 4, 4, "RW", 0, 4'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFMCTL)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFMCTL
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFMSTAT extends uvm_reg;
	uvm_reg_field rank_raa_cnt_gt0;
	uvm_reg_field dbg_raa_cnt;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   rank_raa_cnt_gt0: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {3'b?00};
	      wildcard bins bit_0_wr_as_1 = {3'b?10};
	      wildcard bins bit_0_rd = {3'b??1};
	      wildcard bins bit_1_wr_as_0 = {3'b0?0};
	      wildcard bins bit_1_wr_as_1 = {3'b1?0};
	      wildcard bins bit_1_rd = {3'b??1};
	      option.weight = 6;
	   }
	   dbg_raa_cnt: coverpoint {m_data[26:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {12'b??????????00};
	      wildcard bins bit_0_wr_as_1 = {12'b??????????10};
	      wildcard bins bit_0_rd = {12'b???????????1};
	      wildcard bins bit_1_wr_as_0 = {12'b?????????0?0};
	      wildcard bins bit_1_wr_as_1 = {12'b?????????1?0};
	      wildcard bins bit_1_rd = {12'b???????????1};
	      wildcard bins bit_2_wr_as_0 = {12'b????????0??0};
	      wildcard bins bit_2_wr_as_1 = {12'b????????1??0};
	      wildcard bins bit_2_rd = {12'b???????????1};
	      wildcard bins bit_3_wr_as_0 = {12'b???????0???0};
	      wildcard bins bit_3_wr_as_1 = {12'b???????1???0};
	      wildcard bins bit_3_rd = {12'b???????????1};
	      wildcard bins bit_4_wr_as_0 = {12'b??????0????0};
	      wildcard bins bit_4_wr_as_1 = {12'b??????1????0};
	      wildcard bins bit_4_rd = {12'b???????????1};
	      wildcard bins bit_5_wr_as_0 = {12'b?????0?????0};
	      wildcard bins bit_5_wr_as_1 = {12'b?????1?????0};
	      wildcard bins bit_5_rd = {12'b???????????1};
	      wildcard bins bit_6_wr_as_0 = {12'b????0??????0};
	      wildcard bins bit_6_wr_as_1 = {12'b????1??????0};
	      wildcard bins bit_6_rd = {12'b???????????1};
	      wildcard bins bit_7_wr_as_0 = {12'b???0???????0};
	      wildcard bins bit_7_wr_as_1 = {12'b???1???????0};
	      wildcard bins bit_7_rd = {12'b???????????1};
	      wildcard bins bit_8_wr_as_0 = {12'b??0????????0};
	      wildcard bins bit_8_wr_as_1 = {12'b??1????????0};
	      wildcard bins bit_8_rd = {12'b???????????1};
	      wildcard bins bit_9_wr_as_0 = {12'b?0?????????0};
	      wildcard bins bit_9_wr_as_1 = {12'b?1?????????0};
	      wildcard bins bit_9_rd = {12'b???????????1};
	      wildcard bins bit_10_wr_as_0 = {12'b0??????????0};
	      wildcard bins bit_10_wr_as_1 = {12'b1??????????0};
	      wildcard bins bit_10_rd = {12'b???????????1};
	      option.weight = 33;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_RFMSTAT");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.rank_raa_cnt_gt0 = uvm_reg_field::type_id::create("rank_raa_cnt_gt0",,get_full_name());
      this.rank_raa_cnt_gt0.configure(this, 2, 0, "RO", 0, 2'h0, 1, 0, 1);
      this.dbg_raa_cnt = uvm_reg_field::type_id::create("dbg_raa_cnt",,get_full_name());
      this.dbg_raa_cnt.configure(this, 11, 16, "RO", 0, 11'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFMSTAT)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFMSTAT
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ZQCTL0 extends uvm_reg;
	rand uvm_reg_field zq_resistor_shared;
	rand uvm_reg_field dis_auto_zq;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   zq_resistor_shared: coverpoint {m_data[29:29], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dis_auto_zq: coverpoint {m_data[31:31], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ZQCTL0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.zq_resistor_shared = uvm_reg_field::type_id::create("zq_resistor_shared",,get_full_name());
      this.zq_resistor_shared.configure(this, 1, 29, "RW", 0, 1'h0, 1, 0, 0);
      this.dis_auto_zq = uvm_reg_field::type_id::create("dis_auto_zq",,get_full_name());
      this.dis_auto_zq.configure(this, 1, 31, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ZQCTL0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ZQCTL0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ZQCTL1 extends uvm_reg;
	rand uvm_reg_field zq_reset;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   zq_reset: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ZQCTL1");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.zq_reset = uvm_reg_field::type_id::create("zq_reset",,get_full_name());
      this.zq_reset.configure(this, 1, 0, "W1S", 0, 1'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ZQCTL1)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ZQCTL1
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ZQCTL2 extends uvm_reg;
	rand uvm_reg_field dis_srx_zqcl;
	rand uvm_reg_field dis_srx_zqcl_hwffc;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dis_srx_zqcl: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dis_srx_zqcl_hwffc: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ZQCTL2");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dis_srx_zqcl = uvm_reg_field::type_id::create("dis_srx_zqcl",,get_full_name());
      this.dis_srx_zqcl.configure(this, 1, 0, "RW", 1, 1'h0, 1, 0, 0);
      this.dis_srx_zqcl_hwffc = uvm_reg_field::type_id::create("dis_srx_zqcl_hwffc",,get_full_name());
      this.dis_srx_zqcl_hwffc.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ZQCTL2)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ZQCTL2
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ZQSTAT extends uvm_reg;
	uvm_reg_field zq_reset_busy;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   zq_reset_busy: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ZQSTAT");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.zq_reset_busy = uvm_reg_field::type_id::create("zq_reset_busy",,get_full_name());
      this.zq_reset_busy.configure(this, 1, 0, "RO", 0, 1'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ZQSTAT)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ZQSTAT
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DQSOSCRUNTIME extends uvm_reg;
	rand uvm_reg_field dqsosc_runtime;
	rand uvm_reg_field wck2dqo_runtime;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dqsosc_runtime: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	   wck2dqo_runtime: coverpoint {m_data[23:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_DQSOSCRUNTIME");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dqsosc_runtime = uvm_reg_field::type_id::create("dqsosc_runtime",,get_full_name());
      this.dqsosc_runtime.configure(this, 8, 0, "RW", 1, 8'h40, 1, 0, 1);
      this.wck2dqo_runtime = uvm_reg_field::type_id::create("wck2dqo_runtime",,get_full_name());
      this.wck2dqo_runtime.configure(this, 8, 16, "RW", 1, 8'h40, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DQSOSCRUNTIME)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DQSOSCRUNTIME
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DQSOSCSTAT0 extends uvm_reg;
	uvm_reg_field dqsosc_state;
	uvm_reg_field dqsosc_per_rank_stat;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dqsosc_state: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	   dqsosc_per_rank_stat: coverpoint {m_data[5:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {3'b?00};
	      wildcard bins bit_0_wr_as_1 = {3'b?10};
	      wildcard bins bit_0_rd = {3'b??1};
	      wildcard bins bit_1_wr_as_0 = {3'b0?0};
	      wildcard bins bit_1_wr_as_1 = {3'b1?0};
	      wildcard bins bit_1_rd = {3'b??1};
	      option.weight = 6;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_DQSOSCSTAT0");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dqsosc_state = uvm_reg_field::type_id::create("dqsosc_state",,get_full_name());
      this.dqsosc_state.configure(this, 3, 0, "RO", 0, 3'h0, 1, 0, 0);
      this.dqsosc_per_rank_stat = uvm_reg_field::type_id::create("dqsosc_per_rank_stat",,get_full_name());
      this.dqsosc_per_rank_stat.configure(this, 2, 4, "RO", 0, 2'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DQSOSCSTAT0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DQSOSCSTAT0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DQSOSCCFG0 extends uvm_reg;
	rand uvm_reg_field dis_dqsosc_srx;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dis_dqsosc_srx: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_DQSOSCCFG0");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dis_dqsosc_srx = uvm_reg_field::type_id::create("dis_dqsosc_srx",,get_full_name());
      this.dis_dqsosc_srx.configure(this, 1, 0, "RW", 1, 1'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DQSOSCCFG0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DQSOSCCFG0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED0 extends uvm_reg;
	rand uvm_reg_field dis_opt_wrecc_collision_flush;
	rand uvm_reg_field prefer_write;
	rand uvm_reg_field pageclose;
	rand uvm_reg_field opt_wrcam_fill_level;
	rand uvm_reg_field dis_opt_ntt_by_act;
	rand uvm_reg_field dis_opt_ntt_by_pre;
	rand uvm_reg_field autopre_rmw;
	rand uvm_reg_field lpr_num_entries;
	rand uvm_reg_field lpddr4_opt_act_timing;
	rand uvm_reg_field lpddr5_opt_act_timing;
	rand uvm_reg_field w_starve_free_running;
	rand uvm_reg_field opt_act_lat;
	rand uvm_reg_field prefer_read;
	rand uvm_reg_field dis_speculative_act;
	rand uvm_reg_field opt_vprw_sch;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dis_opt_wrecc_collision_flush: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   prefer_write: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   pageclose: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   opt_wrcam_fill_level: coverpoint {m_data[4:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dis_opt_ntt_by_act: coverpoint {m_data[5:5], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dis_opt_ntt_by_pre: coverpoint {m_data[6:6], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   autopre_rmw: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   lpr_num_entries: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	   lpddr4_opt_act_timing: coverpoint {m_data[15:15], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   lpddr5_opt_act_timing: coverpoint {m_data[16:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   w_starve_free_running: coverpoint {m_data[24:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   opt_act_lat: coverpoint {m_data[27:27], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   prefer_read: coverpoint {m_data[29:29], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dis_speculative_act: coverpoint {m_data[30:30], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   opt_vprw_sch: coverpoint {m_data[31:31], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_SCHED0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dis_opt_wrecc_collision_flush = uvm_reg_field::type_id::create("dis_opt_wrecc_collision_flush",,get_full_name());
      this.dis_opt_wrecc_collision_flush.configure(this, 1, 0, "RW", 1, 1'h0, 1, 0, 0);
      this.prefer_write = uvm_reg_field::type_id::create("prefer_write",,get_full_name());
      this.prefer_write.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.pageclose = uvm_reg_field::type_id::create("pageclose",,get_full_name());
      this.pageclose.configure(this, 1, 2, "RW", 1, 1'h1, 1, 0, 0);
      this.opt_wrcam_fill_level = uvm_reg_field::type_id::create("opt_wrcam_fill_level",,get_full_name());
      this.opt_wrcam_fill_level.configure(this, 1, 4, "RW", 1, 1'h1, 1, 0, 0);
      this.dis_opt_ntt_by_act = uvm_reg_field::type_id::create("dis_opt_ntt_by_act",,get_full_name());
      this.dis_opt_ntt_by_act.configure(this, 1, 5, "RW", 1, 1'h0, 1, 0, 0);
      this.dis_opt_ntt_by_pre = uvm_reg_field::type_id::create("dis_opt_ntt_by_pre",,get_full_name());
      this.dis_opt_ntt_by_pre.configure(this, 1, 6, "RW", 1, 1'h0, 1, 0, 0);
      this.autopre_rmw = uvm_reg_field::type_id::create("autopre_rmw",,get_full_name());
      this.autopre_rmw.configure(this, 1, 7, "RW", 1, 1'h0, 1, 0, 0);
      this.lpr_num_entries = uvm_reg_field::type_id::create("lpr_num_entries",,get_full_name());
      this.lpr_num_entries.configure(this, 6, 8, "RW", 1, 6'h20, 1, 0, 0);
      this.lpddr4_opt_act_timing = uvm_reg_field::type_id::create("lpddr4_opt_act_timing",,get_full_name());
      this.lpddr4_opt_act_timing.configure(this, 1, 15, "RW", 1, 1'h0, 1, 0, 0);
      this.lpddr5_opt_act_timing = uvm_reg_field::type_id::create("lpddr5_opt_act_timing",,get_full_name());
      this.lpddr5_opt_act_timing.configure(this, 1, 16, "RW", 1, 1'h1, 1, 0, 1);
      this.w_starve_free_running = uvm_reg_field::type_id::create("w_starve_free_running",,get_full_name());
      this.w_starve_free_running.configure(this, 1, 24, "RW", 1, 1'h0, 1, 0, 0);
      this.opt_act_lat = uvm_reg_field::type_id::create("opt_act_lat",,get_full_name());
      this.opt_act_lat.configure(this, 1, 27, "RW", 1, 1'h0, 1, 0, 0);
      this.prefer_read = uvm_reg_field::type_id::create("prefer_read",,get_full_name());
      this.prefer_read.configure(this, 1, 29, "RW", 1, 1'h0, 1, 0, 0);
      this.dis_speculative_act = uvm_reg_field::type_id::create("dis_speculative_act",,get_full_name());
      this.dis_speculative_act.configure(this, 1, 30, "RW", 1, 1'h0, 1, 0, 0);
      this.opt_vprw_sch = uvm_reg_field::type_id::create("opt_vprw_sch",,get_full_name());
      this.opt_vprw_sch.configure(this, 1, 31, "RW", 1, 1'h1, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED1 extends uvm_reg;
	rand uvm_reg_field delay_switch_write;
	rand uvm_reg_field visible_window_limit_wr;
	rand uvm_reg_field visible_window_limit_rd;
	rand uvm_reg_field page_hit_limit_wr;
	rand uvm_reg_field page_hit_limit_rd;
	rand uvm_reg_field opt_hit_gt_hpr;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   delay_switch_write: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	   visible_window_limit_wr: coverpoint {m_data[18:16], m_is_read} iff(m_be) {
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
	   visible_window_limit_rd: coverpoint {m_data[22:20], m_is_read} iff(m_be) {
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
	   page_hit_limit_wr: coverpoint {m_data[26:24], m_is_read} iff(m_be) {
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
	   page_hit_limit_rd: coverpoint {m_data[30:28], m_is_read} iff(m_be) {
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
	   opt_hit_gt_hpr: coverpoint {m_data[31:31], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_SCHED1");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.delay_switch_write = uvm_reg_field::type_id::create("delay_switch_write",,get_full_name());
      this.delay_switch_write.configure(this, 4, 12, "RW", 1, 4'h2, 1, 0, 1);
      this.visible_window_limit_wr = uvm_reg_field::type_id::create("visible_window_limit_wr",,get_full_name());
      this.visible_window_limit_wr.configure(this, 3, 16, "RW", 1, 3'h0, 1, 0, 0);
      this.visible_window_limit_rd = uvm_reg_field::type_id::create("visible_window_limit_rd",,get_full_name());
      this.visible_window_limit_rd.configure(this, 3, 20, "RW", 1, 3'h0, 1, 0, 0);
      this.page_hit_limit_wr = uvm_reg_field::type_id::create("page_hit_limit_wr",,get_full_name());
      this.page_hit_limit_wr.configure(this, 3, 24, "RW", 1, 3'h0, 1, 0, 0);
      this.page_hit_limit_rd = uvm_reg_field::type_id::create("page_hit_limit_rd",,get_full_name());
      this.page_hit_limit_rd.configure(this, 3, 28, "RW", 1, 3'h0, 1, 0, 0);
      this.opt_hit_gt_hpr = uvm_reg_field::type_id::create("opt_hit_gt_hpr",,get_full_name());
      this.opt_hit_gt_hpr.configure(this, 1, 31, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED1)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED1
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED3 extends uvm_reg;
	rand uvm_reg_field wrcam_lowthresh;
	rand uvm_reg_field wrcam_highthresh;
	rand uvm_reg_field wr_pghit_num_thresh;
	rand uvm_reg_field rd_pghit_num_thresh;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   wrcam_lowthresh: coverpoint {m_data[5:0], m_is_read} iff(m_be) {
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
	   wrcam_highthresh: coverpoint {m_data[13:8], m_is_read} iff(m_be) {
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
	   wr_pghit_num_thresh: coverpoint {m_data[21:16], m_is_read} iff(m_be) {
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
	   rd_pghit_num_thresh: coverpoint {m_data[29:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_SCHED3");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.wrcam_lowthresh = uvm_reg_field::type_id::create("wrcam_lowthresh",,get_full_name());
      this.wrcam_lowthresh.configure(this, 6, 0, "RW", 1, 6'h8, 1, 0, 1);
      this.wrcam_highthresh = uvm_reg_field::type_id::create("wrcam_highthresh",,get_full_name());
      this.wrcam_highthresh.configure(this, 6, 8, "RW", 1, 6'h2, 1, 0, 1);
      this.wr_pghit_num_thresh = uvm_reg_field::type_id::create("wr_pghit_num_thresh",,get_full_name());
      this.wr_pghit_num_thresh.configure(this, 6, 16, "RW", 1, 6'h4, 1, 0, 1);
      this.rd_pghit_num_thresh = uvm_reg_field::type_id::create("rd_pghit_num_thresh",,get_full_name());
      this.rd_pghit_num_thresh.configure(this, 6, 24, "RW", 1, 6'h4, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED3)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED3
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED4 extends uvm_reg;
	rand uvm_reg_field rd_act_idle_gap;
	rand uvm_reg_field wr_act_idle_gap;
	rand uvm_reg_field rd_page_exp_cycles;
	rand uvm_reg_field wr_page_exp_cycles;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   rd_act_idle_gap: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	   wr_act_idle_gap: coverpoint {m_data[15:8], m_is_read} iff(m_be) {
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
	   rd_page_exp_cycles: coverpoint {m_data[23:16], m_is_read} iff(m_be) {
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
	   wr_page_exp_cycles: coverpoint {m_data[31:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_SCHED4");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.rd_act_idle_gap = uvm_reg_field::type_id::create("rd_act_idle_gap",,get_full_name());
      this.rd_act_idle_gap.configure(this, 8, 0, "RW", 1, 8'h10, 1, 0, 1);
      this.wr_act_idle_gap = uvm_reg_field::type_id::create("wr_act_idle_gap",,get_full_name());
      this.wr_act_idle_gap.configure(this, 8, 8, "RW", 1, 8'h8, 1, 0, 1);
      this.rd_page_exp_cycles = uvm_reg_field::type_id::create("rd_page_exp_cycles",,get_full_name());
      this.rd_page_exp_cycles.configure(this, 8, 16, "RW", 1, 8'h40, 1, 0, 1);
      this.wr_page_exp_cycles = uvm_reg_field::type_id::create("wr_page_exp_cycles",,get_full_name());
      this.wr_page_exp_cycles.configure(this, 8, 24, "RW", 1, 8'h8, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED4)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED4
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED5 extends uvm_reg;
	rand uvm_reg_field wrecc_cam_lowthresh;
	rand uvm_reg_field wrecc_cam_highthresh;
	rand uvm_reg_field dis_opt_loaded_wrecc_cam_fill_level;
	rand uvm_reg_field dis_opt_valid_wrecc_cam_fill_level;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   wrecc_cam_lowthresh: coverpoint {m_data[4:0], m_is_read} iff(m_be) {
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
	   wrecc_cam_highthresh: coverpoint {m_data[12:8], m_is_read} iff(m_be) {
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
	   dis_opt_loaded_wrecc_cam_fill_level: coverpoint {m_data[28:28], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dis_opt_valid_wrecc_cam_fill_level: coverpoint {m_data[29:29], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_SCHED5");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.wrecc_cam_lowthresh = uvm_reg_field::type_id::create("wrecc_cam_lowthresh",,get_full_name());
      this.wrecc_cam_lowthresh.configure(this, 5, 0, "RW", 1, 5'h4, 1, 0, 1);
      this.wrecc_cam_highthresh = uvm_reg_field::type_id::create("wrecc_cam_highthresh",,get_full_name());
      this.wrecc_cam_highthresh.configure(this, 5, 8, "RW", 1, 5'h2, 1, 0, 1);
      this.dis_opt_loaded_wrecc_cam_fill_level = uvm_reg_field::type_id::create("dis_opt_loaded_wrecc_cam_fill_level",,get_full_name());
      this.dis_opt_loaded_wrecc_cam_fill_level.configure(this, 1, 28, "RW", 1, 1'h1, 1, 0, 0);
      this.dis_opt_valid_wrecc_cam_fill_level = uvm_reg_field::type_id::create("dis_opt_valid_wrecc_cam_fill_level",,get_full_name());
      this.dis_opt_valid_wrecc_cam_fill_level.configure(this, 1, 29, "RW", 1, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED5)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED5
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_HWFFCCTL extends uvm_reg;
	rand uvm_reg_field hwffc_en;
	rand uvm_reg_field init_fsp;
	rand uvm_reg_field init_vrcg;
	rand uvm_reg_field target_vrcg;
	rand uvm_reg_field skip_mrw_odtvref;
	rand uvm_reg_field skip_zq_stop_start;
	rand uvm_reg_field zq_interval;
	rand uvm_reg_field hwffc_mode;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   hwffc_en: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   init_fsp: coverpoint {m_data[4:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   init_vrcg: coverpoint {m_data[5:5], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   target_vrcg: coverpoint {m_data[6:6], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   skip_mrw_odtvref: coverpoint {m_data[24:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   skip_zq_stop_start: coverpoint {m_data[25:25], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   zq_interval: coverpoint {m_data[27:26], m_is_read} iff(m_be) {
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
	   hwffc_mode: coverpoint {m_data[31:31], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_HWFFCCTL");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.hwffc_en = uvm_reg_field::type_id::create("hwffc_en",,get_full_name());
      this.hwffc_en.configure(this, 2, 0, "RW", 0, 2'h0, 1, 0, 0);
      this.init_fsp = uvm_reg_field::type_id::create("init_fsp",,get_full_name());
      this.init_fsp.configure(this, 1, 4, "RW", 0, 1'h1, 1, 0, 0);
      this.init_vrcg = uvm_reg_field::type_id::create("init_vrcg",,get_full_name());
      this.init_vrcg.configure(this, 1, 5, "RW", 0, 1'h0, 1, 0, 0);
      this.target_vrcg = uvm_reg_field::type_id::create("target_vrcg",,get_full_name());
      this.target_vrcg.configure(this, 1, 6, "RW", 0, 1'h0, 1, 0, 0);
      this.skip_mrw_odtvref = uvm_reg_field::type_id::create("skip_mrw_odtvref",,get_full_name());
      this.skip_mrw_odtvref.configure(this, 1, 24, "RW", 0, 1'h0, 1, 0, 0);
      this.skip_zq_stop_start = uvm_reg_field::type_id::create("skip_zq_stop_start",,get_full_name());
      this.skip_zq_stop_start.configure(this, 1, 25, "RW", 0, 1'h0, 1, 0, 0);
      this.zq_interval = uvm_reg_field::type_id::create("zq_interval",,get_full_name());
      this.zq_interval.configure(this, 2, 26, "RW", 0, 2'h1, 1, 0, 0);
      this.hwffc_mode = uvm_reg_field::type_id::create("hwffc_mode",,get_full_name());
      this.hwffc_mode.configure(this, 1, 31, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_HWFFCCTL)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_HWFFCCTL
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_HWFFCSTAT extends uvm_reg;
	uvm_reg_field hwffc_in_progress;
	uvm_reg_field hwffc_operating_mode;
	uvm_reg_field current_frequency;
	uvm_reg_field current_fsp;
	uvm_reg_field current_vrcg;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   hwffc_in_progress: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   hwffc_operating_mode: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   current_frequency: coverpoint {m_data[5:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {3'b?00};
	      wildcard bins bit_0_wr_as_1 = {3'b?10};
	      wildcard bins bit_0_rd = {3'b??1};
	      wildcard bins bit_1_wr_as_0 = {3'b0?0};
	      wildcard bins bit_1_wr_as_1 = {3'b1?0};
	      wildcard bins bit_1_rd = {3'b??1};
	      option.weight = 6;
	   }
	   current_fsp: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   current_vrcg: coverpoint {m_data[9:9], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_HWFFCSTAT");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.hwffc_in_progress = uvm_reg_field::type_id::create("hwffc_in_progress",,get_full_name());
      this.hwffc_in_progress.configure(this, 1, 0, "RO", 0, 1'h0, 1, 0, 0);
      this.hwffc_operating_mode = uvm_reg_field::type_id::create("hwffc_operating_mode",,get_full_name());
      this.hwffc_operating_mode.configure(this, 1, 1, "RO", 0, 1'h0, 1, 0, 0);
      this.current_frequency = uvm_reg_field::type_id::create("current_frequency",,get_full_name());
      this.current_frequency.configure(this, 2, 4, "RO", 0, 2'h0, 1, 0, 0);
      this.current_fsp = uvm_reg_field::type_id::create("current_fsp",,get_full_name());
      this.current_fsp.configure(this, 1, 8, "RO", 0, 1'h1, 1, 0, 0);
      this.current_vrcg = uvm_reg_field::type_id::create("current_vrcg",,get_full_name());
      this.current_vrcg.configure(this, 1, 9, "RO", 0, 1'h1, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_HWFFCSTAT)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_HWFFCSTAT
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFILPCFG0 extends uvm_reg;
	rand uvm_reg_field dfi_lp_en_pd;
	rand uvm_reg_field dfi_lp_en_sr;
	rand uvm_reg_field dfi_lp_en_dsm;
	rand uvm_reg_field dfi_lp_en_data;
	rand uvm_reg_field dfi_lp_data_req_en;
	rand uvm_reg_field extra_gap_for_dfi_lp_data;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dfi_lp_en_pd: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dfi_lp_en_sr: coverpoint {m_data[4:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dfi_lp_en_dsm: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dfi_lp_en_data: coverpoint {m_data[16:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dfi_lp_data_req_en: coverpoint {m_data[20:20], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   extra_gap_for_dfi_lp_data: coverpoint {m_data[29:28], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_DFILPCFG0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dfi_lp_en_pd = uvm_reg_field::type_id::create("dfi_lp_en_pd",,get_full_name());
      this.dfi_lp_en_pd.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.dfi_lp_en_sr = uvm_reg_field::type_id::create("dfi_lp_en_sr",,get_full_name());
      this.dfi_lp_en_sr.configure(this, 1, 4, "RW", 0, 1'h0, 1, 0, 0);
      this.dfi_lp_en_dsm = uvm_reg_field::type_id::create("dfi_lp_en_dsm",,get_full_name());
      this.dfi_lp_en_dsm.configure(this, 1, 8, "RW", 0, 1'h0, 1, 0, 1);
      this.dfi_lp_en_data = uvm_reg_field::type_id::create("dfi_lp_en_data",,get_full_name());
      this.dfi_lp_en_data.configure(this, 1, 16, "RW", 0, 1'h0, 1, 0, 0);
      this.dfi_lp_data_req_en = uvm_reg_field::type_id::create("dfi_lp_data_req_en",,get_full_name());
      this.dfi_lp_data_req_en.configure(this, 1, 20, "RW", 0, 1'h1, 1, 0, 0);
      this.extra_gap_for_dfi_lp_data = uvm_reg_field::type_id::create("extra_gap_for_dfi_lp_data",,get_full_name());
      this.extra_gap_for_dfi_lp_data.configure(this, 2, 28, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFILPCFG0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFILPCFG0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFIUPD0 extends uvm_reg;
	rand uvm_reg_field dfi_phyupd_en;
	rand uvm_reg_field ctrlupd_pre_srx;
	rand uvm_reg_field dis_auto_ctrlupd_srx;
	rand uvm_reg_field dis_auto_ctrlupd;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dfi_phyupd_en: coverpoint {m_data[15:15], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ctrlupd_pre_srx: coverpoint {m_data[29:29], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dis_auto_ctrlupd_srx: coverpoint {m_data[30:30], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dis_auto_ctrlupd: coverpoint {m_data[31:31], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_DFIUPD0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dfi_phyupd_en = uvm_reg_field::type_id::create("dfi_phyupd_en",,get_full_name());
      this.dfi_phyupd_en.configure(this, 1, 15, "RW", 0, 1'h1, 1, 0, 1);
      this.ctrlupd_pre_srx = uvm_reg_field::type_id::create("ctrlupd_pre_srx",,get_full_name());
      this.ctrlupd_pre_srx.configure(this, 1, 29, "RW", 0, 1'h0, 1, 0, 0);
      this.dis_auto_ctrlupd_srx = uvm_reg_field::type_id::create("dis_auto_ctrlupd_srx",,get_full_name());
      this.dis_auto_ctrlupd_srx.configure(this, 1, 30, "RW", 1, 1'h0, 1, 0, 0);
      this.dis_auto_ctrlupd = uvm_reg_field::type_id::create("dis_auto_ctrlupd",,get_full_name());
      this.dis_auto_ctrlupd.configure(this, 1, 31, "RW", 1, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFIUPD0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFIUPD0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFIMISC extends uvm_reg;
	rand uvm_reg_field dfi_init_complete_en;
	rand uvm_reg_field phy_dbi_mode;
	rand uvm_reg_field dfi_data_cs_polarity;
	rand uvm_reg_field dfi_reset_n;
	rand uvm_reg_field dfi_init_start;
	rand uvm_reg_field lp_optimized_write;
	rand uvm_reg_field dfi_frequency;
	rand uvm_reg_field dfi_freq_fsp;
	rand uvm_reg_field dfi_channel_mode;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dfi_init_complete_en: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   phy_dbi_mode: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dfi_data_cs_polarity: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dfi_reset_n: coverpoint {m_data[4:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dfi_init_start: coverpoint {m_data[5:5], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   lp_optimized_write: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dfi_frequency: coverpoint {m_data[12:8], m_is_read} iff(m_be) {
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
	   dfi_freq_fsp: coverpoint {m_data[15:14], m_is_read} iff(m_be) {
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
	   dfi_channel_mode: coverpoint {m_data[17:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_DFIMISC");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dfi_init_complete_en = uvm_reg_field::type_id::create("dfi_init_complete_en",,get_full_name());
      this.dfi_init_complete_en.configure(this, 1, 0, "RW", 1, 1'h1, 1, 0, 0);
      this.phy_dbi_mode = uvm_reg_field::type_id::create("phy_dbi_mode",,get_full_name());
      this.phy_dbi_mode.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.dfi_data_cs_polarity = uvm_reg_field::type_id::create("dfi_data_cs_polarity",,get_full_name());
      this.dfi_data_cs_polarity.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
      this.dfi_reset_n = uvm_reg_field::type_id::create("dfi_reset_n",,get_full_name());
      this.dfi_reset_n.configure(this, 1, 4, "RW", 0, 1'h0, 1, 0, 0);
      this.dfi_init_start = uvm_reg_field::type_id::create("dfi_init_start",,get_full_name());
      this.dfi_init_start.configure(this, 1, 5, "RW", 1, 1'h0, 1, 0, 0);
      this.lp_optimized_write = uvm_reg_field::type_id::create("lp_optimized_write",,get_full_name());
      this.lp_optimized_write.configure(this, 1, 7, "RW", 1, 1'h0, 1, 0, 0);
      this.dfi_frequency = uvm_reg_field::type_id::create("dfi_frequency",,get_full_name());
      this.dfi_frequency.configure(this, 5, 8, "RW", 1, 5'h0, 1, 0, 0);
      this.dfi_freq_fsp = uvm_reg_field::type_id::create("dfi_freq_fsp",,get_full_name());
      this.dfi_freq_fsp.configure(this, 2, 14, "RW", 0, 2'h0, 1, 0, 0);
      this.dfi_channel_mode = uvm_reg_field::type_id::create("dfi_channel_mode",,get_full_name());
      this.dfi_channel_mode.configure(this, 2, 16, "RW", 0, 2'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFIMISC)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFIMISC
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFISTAT extends uvm_reg;
	uvm_reg_field dfi_init_complete;
	uvm_reg_field dfi_lp_ctrl_ack_stat;
	uvm_reg_field dfi_lp_data_ack_stat;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dfi_init_complete: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   dfi_lp_ctrl_ack_stat: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   dfi_lp_data_ack_stat: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_DFISTAT");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dfi_init_complete = uvm_reg_field::type_id::create("dfi_init_complete",,get_full_name());
      this.dfi_init_complete.configure(this, 1, 0, "RO", 0, 1'h0, 1, 0, 0);
      this.dfi_lp_ctrl_ack_stat = uvm_reg_field::type_id::create("dfi_lp_ctrl_ack_stat",,get_full_name());
      this.dfi_lp_ctrl_ack_stat.configure(this, 1, 1, "RO", 0, 1'h0, 1, 0, 0);
      this.dfi_lp_data_ack_stat = uvm_reg_field::type_id::create("dfi_lp_data_ack_stat",,get_full_name());
      this.dfi_lp_data_ack_stat.configure(this, 1, 2, "RO", 0, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFISTAT)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFISTAT
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFIPHYMSTR extends uvm_reg;
	rand uvm_reg_field dfi_phymstr_en;
	rand uvm_reg_field dfi_phymstr_blk_ref_x32;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dfi_phymstr_en: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dfi_phymstr_blk_ref_x32: coverpoint {m_data[31:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_DFIPHYMSTR");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dfi_phymstr_en = uvm_reg_field::type_id::create("dfi_phymstr_en",,get_full_name());
      this.dfi_phymstr_en.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 1);
      this.dfi_phymstr_blk_ref_x32 = uvm_reg_field::type_id::create("dfi_phymstr_blk_ref_x32",,get_full_name());
      this.dfi_phymstr_blk_ref_x32.configure(this, 8, 24, "RW", 0, 8'h80, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFIPHYMSTR)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFIPHYMSTR
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_POISONCFG extends uvm_reg;
	rand uvm_reg_field wr_poison_slverr_en;
	rand uvm_reg_field wr_poison_intr_en;
	rand uvm_reg_field wr_poison_intr_clr;
	rand uvm_reg_field rd_poison_slverr_en;
	rand uvm_reg_field rd_poison_intr_en;
	rand uvm_reg_field rd_poison_intr_clr;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   wr_poison_slverr_en: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   wr_poison_intr_en: coverpoint {m_data[4:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   wr_poison_intr_clr: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   rd_poison_slverr_en: coverpoint {m_data[16:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   rd_poison_intr_en: coverpoint {m_data[20:20], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   rd_poison_intr_clr: coverpoint {m_data[24:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_POISONCFG");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.wr_poison_slverr_en = uvm_reg_field::type_id::create("wr_poison_slverr_en",,get_full_name());
      this.wr_poison_slverr_en.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 0);
      this.wr_poison_intr_en = uvm_reg_field::type_id::create("wr_poison_intr_en",,get_full_name());
      this.wr_poison_intr_en.configure(this, 1, 4, "RW", 0, 1'h1, 1, 0, 0);
      this.wr_poison_intr_clr = uvm_reg_field::type_id::create("wr_poison_intr_clr",,get_full_name());
      this.wr_poison_intr_clr.configure(this, 1, 8, "W1C", 0, 1'h0, 1, 0, 1);
      this.rd_poison_slverr_en = uvm_reg_field::type_id::create("rd_poison_slverr_en",,get_full_name());
      this.rd_poison_slverr_en.configure(this, 1, 16, "RW", 0, 1'h1, 1, 0, 0);
      this.rd_poison_intr_en = uvm_reg_field::type_id::create("rd_poison_intr_en",,get_full_name());
      this.rd_poison_intr_en.configure(this, 1, 20, "RW", 0, 1'h1, 1, 0, 0);
      this.rd_poison_intr_clr = uvm_reg_field::type_id::create("rd_poison_intr_clr",,get_full_name());
      this.rd_poison_intr_clr.configure(this, 1, 24, "W1C", 0, 1'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_POISONCFG)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_POISONCFG
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_POISONSTAT extends uvm_reg;
	uvm_reg_field wr_poison_intr_0;
	uvm_reg_field rd_poison_intr_0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   wr_poison_intr_0: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   rd_poison_intr_0: coverpoint {m_data[16:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_POISONSTAT");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.wr_poison_intr_0 = uvm_reg_field::type_id::create("wr_poison_intr_0",,get_full_name());
      this.wr_poison_intr_0.configure(this, 1, 0, "RO", 0, 1'h0, 1, 0, 1);
      this.rd_poison_intr_0 = uvm_reg_field::type_id::create("rd_poison_intr_0",,get_full_name());
      this.rd_poison_intr_0.configure(this, 1, 16, "RO", 0, 1'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_POISONSTAT)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_POISONSTAT
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCFG0 extends uvm_reg;
	rand uvm_reg_field ecc_mode;
	rand uvm_reg_field ecc_ap_en;
	rand uvm_reg_field ecc_region_remap_en;
	rand uvm_reg_field ecc_region_map;
	rand uvm_reg_field blk_channel_idle_time_x32;
	rand uvm_reg_field ecc_ap_err_threshold;
	rand uvm_reg_field ecc_region_map_other;
	rand uvm_reg_field ecc_region_map_granu;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_mode: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	   ecc_ap_en: coverpoint {m_data[6:6], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ecc_region_remap_en: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ecc_region_map: coverpoint {m_data[14:8], m_is_read} iff(m_be) {
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
	   blk_channel_idle_time_x32: coverpoint {m_data[21:16], m_is_read} iff(m_be) {
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
	   ecc_ap_err_threshold: coverpoint {m_data[26:24], m_is_read} iff(m_be) {
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
	   ecc_region_map_other: coverpoint {m_data[29:29], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ecc_region_map_granu: coverpoint {m_data[31:30], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCCFG0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_mode = uvm_reg_field::type_id::create("ecc_mode",,get_full_name());
      this.ecc_mode.configure(this, 3, 0, "RW", 0, 3'h0, 1, 0, 0);
      this.ecc_ap_en = uvm_reg_field::type_id::create("ecc_ap_en",,get_full_name());
      this.ecc_ap_en.configure(this, 1, 6, "RW", 0, 1'h1, 1, 0, 0);
      this.ecc_region_remap_en = uvm_reg_field::type_id::create("ecc_region_remap_en",,get_full_name());
      this.ecc_region_remap_en.configure(this, 1, 7, "RW", 0, 1'h0, 1, 0, 0);
      this.ecc_region_map = uvm_reg_field::type_id::create("ecc_region_map",,get_full_name());
      this.ecc_region_map.configure(this, 7, 8, "RW", 1, 7'h7f, 1, 0, 1);
      this.blk_channel_idle_time_x32 = uvm_reg_field::type_id::create("blk_channel_idle_time_x32",,get_full_name());
      this.blk_channel_idle_time_x32.configure(this, 6, 16, "RW", 1, 6'h3f, 1, 0, 1);
      this.ecc_ap_err_threshold = uvm_reg_field::type_id::create("ecc_ap_err_threshold",,get_full_name());
      this.ecc_ap_err_threshold.configure(this, 3, 24, "RW", 0, 3'h3, 1, 0, 0);
      this.ecc_region_map_other = uvm_reg_field::type_id::create("ecc_region_map_other",,get_full_name());
      this.ecc_region_map_other.configure(this, 1, 29, "RW", 0, 1'h0, 1, 0, 0);
      this.ecc_region_map_granu = uvm_reg_field::type_id::create("ecc_region_map_granu",,get_full_name());
      this.ecc_region_map_granu.configure(this, 2, 30, "RW", 0, 2'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCFG0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCFG0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCFG1 extends uvm_reg;
	rand uvm_reg_field data_poison_en;
	rand uvm_reg_field data_poison_bit;
	rand uvm_reg_field ecc_region_parity_lock;
	rand uvm_reg_field ecc_region_waste_lock;
	rand uvm_reg_field med_ecc_en;
	rand uvm_reg_field blk_channel_active_term;
	rand uvm_reg_field active_blk_channel;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   data_poison_en: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   data_poison_bit: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ecc_region_parity_lock: coverpoint {m_data[4:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ecc_region_waste_lock: coverpoint {m_data[5:5], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   med_ecc_en: coverpoint {m_data[6:6], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   blk_channel_active_term: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   active_blk_channel: coverpoint {m_data[12:8], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCCFG1");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.data_poison_en = uvm_reg_field::type_id::create("data_poison_en",,get_full_name());
      this.data_poison_en.configure(this, 1, 0, "RW", 1, 1'h0, 1, 0, 0);
      this.data_poison_bit = uvm_reg_field::type_id::create("data_poison_bit",,get_full_name());
      this.data_poison_bit.configure(this, 1, 1, "RW", 1, 1'h0, 1, 0, 0);
      this.ecc_region_parity_lock = uvm_reg_field::type_id::create("ecc_region_parity_lock",,get_full_name());
      this.ecc_region_parity_lock.configure(this, 1, 4, "RW", 1, 1'h1, 1, 0, 0);
      this.ecc_region_waste_lock = uvm_reg_field::type_id::create("ecc_region_waste_lock",,get_full_name());
      this.ecc_region_waste_lock.configure(this, 1, 5, "RW", 1, 1'h1, 1, 0, 0);
      this.med_ecc_en = uvm_reg_field::type_id::create("med_ecc_en",,get_full_name());
      this.med_ecc_en.configure(this, 1, 6, "RW", 1, 1'h0, 1, 0, 0);
      this.blk_channel_active_term = uvm_reg_field::type_id::create("blk_channel_active_term",,get_full_name());
      this.blk_channel_active_term.configure(this, 1, 7, "RW", 1, 1'h1, 1, 0, 0);
      this.active_blk_channel = uvm_reg_field::type_id::create("active_blk_channel",,get_full_name());
      this.active_blk_channel.configure(this, 5, 8, "RW", 1, 5'h1f, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCFG1)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCFG1
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCSTAT extends uvm_reg;
	uvm_reg_field ecc_corrected_bit_num;
	uvm_reg_field ecc_corrected_err;
	uvm_reg_field ecc_uncorrected_err;
	uvm_reg_field sbr_read_ecc_ce;
	uvm_reg_field sbr_read_ecc_ue;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_corrected_bit_num: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {8'b??????00};
	      wildcard bins bit_0_wr_as_1 = {8'b??????10};
	      wildcard bins bit_0_rd = {8'b???????1};
	      wildcard bins bit_1_wr_as_0 = {8'b?????0?0};
	      wildcard bins bit_1_wr_as_1 = {8'b?????1?0};
	      wildcard bins bit_1_rd = {8'b???????1};
	      wildcard bins bit_2_wr_as_0 = {8'b????0??0};
	      wildcard bins bit_2_wr_as_1 = {8'b????1??0};
	      wildcard bins bit_2_rd = {8'b???????1};
	      wildcard bins bit_3_wr_as_0 = {8'b???0???0};
	      wildcard bins bit_3_wr_as_1 = {8'b???1???0};
	      wildcard bins bit_3_rd = {8'b???????1};
	      wildcard bins bit_4_wr_as_0 = {8'b??0????0};
	      wildcard bins bit_4_wr_as_1 = {8'b??1????0};
	      wildcard bins bit_4_rd = {8'b???????1};
	      wildcard bins bit_5_wr_as_0 = {8'b?0?????0};
	      wildcard bins bit_5_wr_as_1 = {8'b?1?????0};
	      wildcard bins bit_5_rd = {8'b???????1};
	      wildcard bins bit_6_wr_as_0 = {8'b0??????0};
	      wildcard bins bit_6_wr_as_1 = {8'b1??????0};
	      wildcard bins bit_6_rd = {8'b???????1};
	      option.weight = 21;
	   }
	   ecc_corrected_err: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   ecc_uncorrected_err: coverpoint {m_data[16:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   sbr_read_ecc_ce: coverpoint {m_data[24:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   sbr_read_ecc_ue: coverpoint {m_data[25:25], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCSTAT");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_corrected_bit_num = uvm_reg_field::type_id::create("ecc_corrected_bit_num",,get_full_name());
      this.ecc_corrected_bit_num.configure(this, 7, 0, "RO", 0, 7'h0, 1, 0, 1);
      this.ecc_corrected_err = uvm_reg_field::type_id::create("ecc_corrected_err",,get_full_name());
      this.ecc_corrected_err.configure(this, 1, 8, "RO", 0, 1'h0, 1, 0, 1);
      this.ecc_uncorrected_err = uvm_reg_field::type_id::create("ecc_uncorrected_err",,get_full_name());
      this.ecc_uncorrected_err.configure(this, 1, 16, "RO", 0, 1'h0, 1, 0, 1);
      this.sbr_read_ecc_ce = uvm_reg_field::type_id::create("sbr_read_ecc_ce",,get_full_name());
      this.sbr_read_ecc_ce.configure(this, 1, 24, "RO", 0, 1'h0, 1, 0, 0);
      this.sbr_read_ecc_ue = uvm_reg_field::type_id::create("sbr_read_ecc_ue",,get_full_name());
      this.sbr_read_ecc_ue.configure(this, 1, 25, "RO", 0, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCSTAT)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCSTAT
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCTL extends uvm_reg;
	rand uvm_reg_field ecc_corrected_err_clr;
	rand uvm_reg_field ecc_uncorrected_err_clr;
	rand uvm_reg_field ecc_corr_err_cnt_clr;
	rand uvm_reg_field ecc_uncorr_err_cnt_clr;
	rand uvm_reg_field ecc_ap_err_intr_clr;
	rand uvm_reg_field ecc_corrected_err_intr_en;
	rand uvm_reg_field ecc_uncorrected_err_intr_en;
	rand uvm_reg_field ecc_ap_err_intr_en;
	rand uvm_reg_field ecc_corrected_err_intr_force;
	rand uvm_reg_field ecc_uncorrected_err_intr_force;
	rand uvm_reg_field ecc_ap_err_intr_force;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_corrected_err_clr: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ecc_uncorrected_err_clr: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ecc_corr_err_cnt_clr: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ecc_uncorr_err_cnt_clr: coverpoint {m_data[3:3], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ecc_ap_err_intr_clr: coverpoint {m_data[4:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ecc_corrected_err_intr_en: coverpoint {m_data[8:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ecc_uncorrected_err_intr_en: coverpoint {m_data[9:9], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ecc_ap_err_intr_en: coverpoint {m_data[10:10], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ecc_corrected_err_intr_force: coverpoint {m_data[16:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ecc_uncorrected_err_intr_force: coverpoint {m_data[17:17], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ecc_ap_err_intr_force: coverpoint {m_data[18:18], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCCTL");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_corrected_err_clr = uvm_reg_field::type_id::create("ecc_corrected_err_clr",,get_full_name());
      this.ecc_corrected_err_clr.configure(this, 1, 0, "W1C", 0, 1'h0, 1, 0, 0);
      this.ecc_uncorrected_err_clr = uvm_reg_field::type_id::create("ecc_uncorrected_err_clr",,get_full_name());
      this.ecc_uncorrected_err_clr.configure(this, 1, 1, "W1C", 0, 1'h0, 1, 0, 0);
      this.ecc_corr_err_cnt_clr = uvm_reg_field::type_id::create("ecc_corr_err_cnt_clr",,get_full_name());
      this.ecc_corr_err_cnt_clr.configure(this, 1, 2, "W1C", 0, 1'h0, 1, 0, 0);
      this.ecc_uncorr_err_cnt_clr = uvm_reg_field::type_id::create("ecc_uncorr_err_cnt_clr",,get_full_name());
      this.ecc_uncorr_err_cnt_clr.configure(this, 1, 3, "W1C", 0, 1'h0, 1, 0, 0);
      this.ecc_ap_err_intr_clr = uvm_reg_field::type_id::create("ecc_ap_err_intr_clr",,get_full_name());
      this.ecc_ap_err_intr_clr.configure(this, 1, 4, "W1C", 0, 1'h0, 1, 0, 0);
      this.ecc_corrected_err_intr_en = uvm_reg_field::type_id::create("ecc_corrected_err_intr_en",,get_full_name());
      this.ecc_corrected_err_intr_en.configure(this, 1, 8, "RW", 0, 1'h1, 1, 0, 0);
      this.ecc_uncorrected_err_intr_en = uvm_reg_field::type_id::create("ecc_uncorrected_err_intr_en",,get_full_name());
      this.ecc_uncorrected_err_intr_en.configure(this, 1, 9, "RW", 0, 1'h1, 1, 0, 0);
      this.ecc_ap_err_intr_en = uvm_reg_field::type_id::create("ecc_ap_err_intr_en",,get_full_name());
      this.ecc_ap_err_intr_en.configure(this, 1, 10, "RW", 0, 1'h1, 1, 0, 0);
      this.ecc_corrected_err_intr_force = uvm_reg_field::type_id::create("ecc_corrected_err_intr_force",,get_full_name());
      this.ecc_corrected_err_intr_force.configure(this, 1, 16, "W1C", 0, 1'h0, 1, 0, 0);
      this.ecc_uncorrected_err_intr_force = uvm_reg_field::type_id::create("ecc_uncorrected_err_intr_force",,get_full_name());
      this.ecc_uncorrected_err_intr_force.configure(this, 1, 17, "W1C", 0, 1'h0, 1, 0, 0);
      this.ecc_ap_err_intr_force = uvm_reg_field::type_id::create("ecc_ap_err_intr_force",,get_full_name());
      this.ecc_ap_err_intr_force.configure(this, 1, 18, "W1C", 0, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCTL)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCTL
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCERRCNT extends uvm_reg;
	uvm_reg_field ecc_corr_err_cnt;
	uvm_reg_field ecc_uncorr_err_cnt;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_corr_err_cnt: coverpoint {m_data[15:0], m_is_read} iff(m_be) {
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
	   ecc_uncorr_err_cnt: coverpoint {m_data[31:16], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCERRCNT");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_corr_err_cnt = uvm_reg_field::type_id::create("ecc_corr_err_cnt",,get_full_name());
      this.ecc_corr_err_cnt.configure(this, 16, 0, "RO", 0, 16'h0, 1, 0, 1);
      this.ecc_uncorr_err_cnt = uvm_reg_field::type_id::create("ecc_uncorr_err_cnt",,get_full_name());
      this.ecc_uncorr_err_cnt.configure(this, 16, 16, "RO", 0, 16'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCERRCNT)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCERRCNT
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCADDR0 extends uvm_reg;
	uvm_reg_field ecc_corr_row;
	uvm_reg_field ecc_corr_rank;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_corr_row: coverpoint {m_data[17:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {19'b?????????????????00};
	      wildcard bins bit_0_wr_as_1 = {19'b?????????????????10};
	      wildcard bins bit_0_rd = {19'b??????????????????1};
	      wildcard bins bit_1_wr_as_0 = {19'b????????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {19'b????????????????1?0};
	      wildcard bins bit_1_rd = {19'b??????????????????1};
	      wildcard bins bit_2_wr_as_0 = {19'b???????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {19'b???????????????1??0};
	      wildcard bins bit_2_rd = {19'b??????????????????1};
	      wildcard bins bit_3_wr_as_0 = {19'b??????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {19'b??????????????1???0};
	      wildcard bins bit_3_rd = {19'b??????????????????1};
	      wildcard bins bit_4_wr_as_0 = {19'b?????????????0????0};
	      wildcard bins bit_4_wr_as_1 = {19'b?????????????1????0};
	      wildcard bins bit_4_rd = {19'b??????????????????1};
	      wildcard bins bit_5_wr_as_0 = {19'b????????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {19'b????????????1?????0};
	      wildcard bins bit_5_rd = {19'b??????????????????1};
	      wildcard bins bit_6_wr_as_0 = {19'b???????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {19'b???????????1??????0};
	      wildcard bins bit_6_rd = {19'b??????????????????1};
	      wildcard bins bit_7_wr_as_0 = {19'b??????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {19'b??????????1???????0};
	      wildcard bins bit_7_rd = {19'b??????????????????1};
	      wildcard bins bit_8_wr_as_0 = {19'b?????????0????????0};
	      wildcard bins bit_8_wr_as_1 = {19'b?????????1????????0};
	      wildcard bins bit_8_rd = {19'b??????????????????1};
	      wildcard bins bit_9_wr_as_0 = {19'b????????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {19'b????????1?????????0};
	      wildcard bins bit_9_rd = {19'b??????????????????1};
	      wildcard bins bit_10_wr_as_0 = {19'b???????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {19'b???????1??????????0};
	      wildcard bins bit_10_rd = {19'b??????????????????1};
	      wildcard bins bit_11_wr_as_0 = {19'b??????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {19'b??????1???????????0};
	      wildcard bins bit_11_rd = {19'b??????????????????1};
	      wildcard bins bit_12_wr_as_0 = {19'b?????0????????????0};
	      wildcard bins bit_12_wr_as_1 = {19'b?????1????????????0};
	      wildcard bins bit_12_rd = {19'b??????????????????1};
	      wildcard bins bit_13_wr_as_0 = {19'b????0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {19'b????1?????????????0};
	      wildcard bins bit_13_rd = {19'b??????????????????1};
	      wildcard bins bit_14_wr_as_0 = {19'b???0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {19'b???1??????????????0};
	      wildcard bins bit_14_rd = {19'b??????????????????1};
	      wildcard bins bit_15_wr_as_0 = {19'b??0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {19'b??1???????????????0};
	      wildcard bins bit_15_rd = {19'b??????????????????1};
	      wildcard bins bit_16_wr_as_0 = {19'b?0????????????????0};
	      wildcard bins bit_16_wr_as_1 = {19'b?1????????????????0};
	      wildcard bins bit_16_rd = {19'b??????????????????1};
	      wildcard bins bit_17_wr_as_0 = {19'b0?????????????????0};
	      wildcard bins bit_17_wr_as_1 = {19'b1?????????????????0};
	      wildcard bins bit_17_rd = {19'b??????????????????1};
	      option.weight = 54;
	   }
	   ecc_corr_rank: coverpoint {m_data[24:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCCADDR0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_corr_row = uvm_reg_field::type_id::create("ecc_corr_row",,get_full_name());
      this.ecc_corr_row.configure(this, 18, 0, "RO", 0, 18'h0, 1, 0, 1);
      this.ecc_corr_rank = uvm_reg_field::type_id::create("ecc_corr_rank",,get_full_name());
      this.ecc_corr_rank.configure(this, 1, 24, "RO", 0, 1'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCADDR0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCADDR0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCADDR1 extends uvm_reg;
	uvm_reg_field ecc_corr_col;
	uvm_reg_field ecc_corr_bank;
	uvm_reg_field ecc_corr_bg;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_corr_col: coverpoint {m_data[10:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {12'b??????????00};
	      wildcard bins bit_0_wr_as_1 = {12'b??????????10};
	      wildcard bins bit_0_rd = {12'b???????????1};
	      wildcard bins bit_1_wr_as_0 = {12'b?????????0?0};
	      wildcard bins bit_1_wr_as_1 = {12'b?????????1?0};
	      wildcard bins bit_1_rd = {12'b???????????1};
	      wildcard bins bit_2_wr_as_0 = {12'b????????0??0};
	      wildcard bins bit_2_wr_as_1 = {12'b????????1??0};
	      wildcard bins bit_2_rd = {12'b???????????1};
	      wildcard bins bit_3_wr_as_0 = {12'b???????0???0};
	      wildcard bins bit_3_wr_as_1 = {12'b???????1???0};
	      wildcard bins bit_3_rd = {12'b???????????1};
	      wildcard bins bit_4_wr_as_0 = {12'b??????0????0};
	      wildcard bins bit_4_wr_as_1 = {12'b??????1????0};
	      wildcard bins bit_4_rd = {12'b???????????1};
	      wildcard bins bit_5_wr_as_0 = {12'b?????0?????0};
	      wildcard bins bit_5_wr_as_1 = {12'b?????1?????0};
	      wildcard bins bit_5_rd = {12'b???????????1};
	      wildcard bins bit_6_wr_as_0 = {12'b????0??????0};
	      wildcard bins bit_6_wr_as_1 = {12'b????1??????0};
	      wildcard bins bit_6_rd = {12'b???????????1};
	      wildcard bins bit_7_wr_as_0 = {12'b???0???????0};
	      wildcard bins bit_7_wr_as_1 = {12'b???1???????0};
	      wildcard bins bit_7_rd = {12'b???????????1};
	      wildcard bins bit_8_wr_as_0 = {12'b??0????????0};
	      wildcard bins bit_8_wr_as_1 = {12'b??1????????0};
	      wildcard bins bit_8_rd = {12'b???????????1};
	      wildcard bins bit_9_wr_as_0 = {12'b?0?????????0};
	      wildcard bins bit_9_wr_as_1 = {12'b?1?????????0};
	      wildcard bins bit_9_rd = {12'b???????????1};
	      wildcard bins bit_10_wr_as_0 = {12'b0??????????0};
	      wildcard bins bit_10_wr_as_1 = {12'b1??????????0};
	      wildcard bins bit_10_rd = {12'b???????????1};
	      option.weight = 33;
	   }
	   ecc_corr_bank: coverpoint {m_data[18:16], m_is_read} iff(m_be) {
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
	   ecc_corr_bg: coverpoint {m_data[25:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {3'b?00};
	      wildcard bins bit_0_wr_as_1 = {3'b?10};
	      wildcard bins bit_0_rd = {3'b??1};
	      wildcard bins bit_1_wr_as_0 = {3'b0?0};
	      wildcard bins bit_1_wr_as_1 = {3'b1?0};
	      wildcard bins bit_1_rd = {3'b??1};
	      option.weight = 6;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCCADDR1");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_corr_col = uvm_reg_field::type_id::create("ecc_corr_col",,get_full_name());
      this.ecc_corr_col.configure(this, 11, 0, "RO", 0, 11'h0, 1, 0, 1);
      this.ecc_corr_bank = uvm_reg_field::type_id::create("ecc_corr_bank",,get_full_name());
      this.ecc_corr_bank.configure(this, 3, 16, "RO", 0, 3'h0, 1, 0, 1);
      this.ecc_corr_bg = uvm_reg_field::type_id::create("ecc_corr_bg",,get_full_name());
      this.ecc_corr_bg.configure(this, 2, 24, "RO", 0, 2'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCADDR1)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCADDR1
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCSYN0 extends uvm_reg;
	uvm_reg_field ecc_corr_syndromes_31_0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_corr_syndromes_31_0: coverpoint {m_data[31:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {33'b???????????????????????????????00};
	      wildcard bins bit_0_wr_as_1 = {33'b???????????????????????????????10};
	      wildcard bins bit_0_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_1_wr_as_0 = {33'b??????????????????????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {33'b??????????????????????????????1?0};
	      wildcard bins bit_1_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_2_wr_as_0 = {33'b?????????????????????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {33'b?????????????????????????????1??0};
	      wildcard bins bit_2_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_3_wr_as_0 = {33'b????????????????????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {33'b????????????????????????????1???0};
	      wildcard bins bit_3_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_4_wr_as_0 = {33'b???????????????????????????0????0};
	      wildcard bins bit_4_wr_as_1 = {33'b???????????????????????????1????0};
	      wildcard bins bit_4_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_5_wr_as_0 = {33'b??????????????????????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {33'b??????????????????????????1?????0};
	      wildcard bins bit_5_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_6_wr_as_0 = {33'b?????????????????????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {33'b?????????????????????????1??????0};
	      wildcard bins bit_6_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_7_wr_as_0 = {33'b????????????????????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {33'b????????????????????????1???????0};
	      wildcard bins bit_7_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_8_wr_as_0 = {33'b???????????????????????0????????0};
	      wildcard bins bit_8_wr_as_1 = {33'b???????????????????????1????????0};
	      wildcard bins bit_8_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_9_wr_as_0 = {33'b??????????????????????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {33'b??????????????????????1?????????0};
	      wildcard bins bit_9_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_10_wr_as_0 = {33'b?????????????????????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {33'b?????????????????????1??????????0};
	      wildcard bins bit_10_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_11_wr_as_0 = {33'b????????????????????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {33'b????????????????????1???????????0};
	      wildcard bins bit_11_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_12_wr_as_0 = {33'b???????????????????0????????????0};
	      wildcard bins bit_12_wr_as_1 = {33'b???????????????????1????????????0};
	      wildcard bins bit_12_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_13_wr_as_0 = {33'b??????????????????0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {33'b??????????????????1?????????????0};
	      wildcard bins bit_13_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_14_wr_as_0 = {33'b?????????????????0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {33'b?????????????????1??????????????0};
	      wildcard bins bit_14_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_15_wr_as_0 = {33'b????????????????0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {33'b????????????????1???????????????0};
	      wildcard bins bit_15_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_16_wr_as_0 = {33'b???????????????0????????????????0};
	      wildcard bins bit_16_wr_as_1 = {33'b???????????????1????????????????0};
	      wildcard bins bit_16_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_17_wr_as_0 = {33'b??????????????0?????????????????0};
	      wildcard bins bit_17_wr_as_1 = {33'b??????????????1?????????????????0};
	      wildcard bins bit_17_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_18_wr_as_0 = {33'b?????????????0??????????????????0};
	      wildcard bins bit_18_wr_as_1 = {33'b?????????????1??????????????????0};
	      wildcard bins bit_18_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_19_wr_as_0 = {33'b????????????0???????????????????0};
	      wildcard bins bit_19_wr_as_1 = {33'b????????????1???????????????????0};
	      wildcard bins bit_19_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_20_wr_as_0 = {33'b???????????0????????????????????0};
	      wildcard bins bit_20_wr_as_1 = {33'b???????????1????????????????????0};
	      wildcard bins bit_20_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_21_wr_as_0 = {33'b??????????0?????????????????????0};
	      wildcard bins bit_21_wr_as_1 = {33'b??????????1?????????????????????0};
	      wildcard bins bit_21_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_22_wr_as_0 = {33'b?????????0??????????????????????0};
	      wildcard bins bit_22_wr_as_1 = {33'b?????????1??????????????????????0};
	      wildcard bins bit_22_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_23_wr_as_0 = {33'b????????0???????????????????????0};
	      wildcard bins bit_23_wr_as_1 = {33'b????????1???????????????????????0};
	      wildcard bins bit_23_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_24_wr_as_0 = {33'b???????0????????????????????????0};
	      wildcard bins bit_24_wr_as_1 = {33'b???????1????????????????????????0};
	      wildcard bins bit_24_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_25_wr_as_0 = {33'b??????0?????????????????????????0};
	      wildcard bins bit_25_wr_as_1 = {33'b??????1?????????????????????????0};
	      wildcard bins bit_25_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_26_wr_as_0 = {33'b?????0??????????????????????????0};
	      wildcard bins bit_26_wr_as_1 = {33'b?????1??????????????????????????0};
	      wildcard bins bit_26_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_27_wr_as_0 = {33'b????0???????????????????????????0};
	      wildcard bins bit_27_wr_as_1 = {33'b????1???????????????????????????0};
	      wildcard bins bit_27_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_28_wr_as_0 = {33'b???0????????????????????????????0};
	      wildcard bins bit_28_wr_as_1 = {33'b???1????????????????????????????0};
	      wildcard bins bit_28_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_29_wr_as_0 = {33'b??0?????????????????????????????0};
	      wildcard bins bit_29_wr_as_1 = {33'b??1?????????????????????????????0};
	      wildcard bins bit_29_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_30_wr_as_0 = {33'b?0??????????????????????????????0};
	      wildcard bins bit_30_wr_as_1 = {33'b?1??????????????????????????????0};
	      wildcard bins bit_30_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_31_wr_as_0 = {33'b0???????????????????????????????0};
	      wildcard bins bit_31_wr_as_1 = {33'b1???????????????????????????????0};
	      wildcard bins bit_31_rd = {33'b????????????????????????????????1};
	      option.weight = 96;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCCSYN0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_corr_syndromes_31_0 = uvm_reg_field::type_id::create("ecc_corr_syndromes_31_0",,get_full_name());
      this.ecc_corr_syndromes_31_0.configure(this, 32, 0, "RO", 0, 32'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCSYN0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCSYN0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCSYN1 extends uvm_reg;
	uvm_reg_field ecc_corr_syndromes_63_32;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_corr_syndromes_63_32: coverpoint {m_data[31:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {33'b???????????????????????????????00};
	      wildcard bins bit_0_wr_as_1 = {33'b???????????????????????????????10};
	      wildcard bins bit_0_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_1_wr_as_0 = {33'b??????????????????????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {33'b??????????????????????????????1?0};
	      wildcard bins bit_1_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_2_wr_as_0 = {33'b?????????????????????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {33'b?????????????????????????????1??0};
	      wildcard bins bit_2_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_3_wr_as_0 = {33'b????????????????????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {33'b????????????????????????????1???0};
	      wildcard bins bit_3_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_4_wr_as_0 = {33'b???????????????????????????0????0};
	      wildcard bins bit_4_wr_as_1 = {33'b???????????????????????????1????0};
	      wildcard bins bit_4_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_5_wr_as_0 = {33'b??????????????????????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {33'b??????????????????????????1?????0};
	      wildcard bins bit_5_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_6_wr_as_0 = {33'b?????????????????????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {33'b?????????????????????????1??????0};
	      wildcard bins bit_6_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_7_wr_as_0 = {33'b????????????????????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {33'b????????????????????????1???????0};
	      wildcard bins bit_7_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_8_wr_as_0 = {33'b???????????????????????0????????0};
	      wildcard bins bit_8_wr_as_1 = {33'b???????????????????????1????????0};
	      wildcard bins bit_8_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_9_wr_as_0 = {33'b??????????????????????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {33'b??????????????????????1?????????0};
	      wildcard bins bit_9_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_10_wr_as_0 = {33'b?????????????????????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {33'b?????????????????????1??????????0};
	      wildcard bins bit_10_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_11_wr_as_0 = {33'b????????????????????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {33'b????????????????????1???????????0};
	      wildcard bins bit_11_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_12_wr_as_0 = {33'b???????????????????0????????????0};
	      wildcard bins bit_12_wr_as_1 = {33'b???????????????????1????????????0};
	      wildcard bins bit_12_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_13_wr_as_0 = {33'b??????????????????0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {33'b??????????????????1?????????????0};
	      wildcard bins bit_13_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_14_wr_as_0 = {33'b?????????????????0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {33'b?????????????????1??????????????0};
	      wildcard bins bit_14_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_15_wr_as_0 = {33'b????????????????0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {33'b????????????????1???????????????0};
	      wildcard bins bit_15_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_16_wr_as_0 = {33'b???????????????0????????????????0};
	      wildcard bins bit_16_wr_as_1 = {33'b???????????????1????????????????0};
	      wildcard bins bit_16_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_17_wr_as_0 = {33'b??????????????0?????????????????0};
	      wildcard bins bit_17_wr_as_1 = {33'b??????????????1?????????????????0};
	      wildcard bins bit_17_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_18_wr_as_0 = {33'b?????????????0??????????????????0};
	      wildcard bins bit_18_wr_as_1 = {33'b?????????????1??????????????????0};
	      wildcard bins bit_18_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_19_wr_as_0 = {33'b????????????0???????????????????0};
	      wildcard bins bit_19_wr_as_1 = {33'b????????????1???????????????????0};
	      wildcard bins bit_19_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_20_wr_as_0 = {33'b???????????0????????????????????0};
	      wildcard bins bit_20_wr_as_1 = {33'b???????????1????????????????????0};
	      wildcard bins bit_20_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_21_wr_as_0 = {33'b??????????0?????????????????????0};
	      wildcard bins bit_21_wr_as_1 = {33'b??????????1?????????????????????0};
	      wildcard bins bit_21_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_22_wr_as_0 = {33'b?????????0??????????????????????0};
	      wildcard bins bit_22_wr_as_1 = {33'b?????????1??????????????????????0};
	      wildcard bins bit_22_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_23_wr_as_0 = {33'b????????0???????????????????????0};
	      wildcard bins bit_23_wr_as_1 = {33'b????????1???????????????????????0};
	      wildcard bins bit_23_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_24_wr_as_0 = {33'b???????0????????????????????????0};
	      wildcard bins bit_24_wr_as_1 = {33'b???????1????????????????????????0};
	      wildcard bins bit_24_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_25_wr_as_0 = {33'b??????0?????????????????????????0};
	      wildcard bins bit_25_wr_as_1 = {33'b??????1?????????????????????????0};
	      wildcard bins bit_25_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_26_wr_as_0 = {33'b?????0??????????????????????????0};
	      wildcard bins bit_26_wr_as_1 = {33'b?????1??????????????????????????0};
	      wildcard bins bit_26_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_27_wr_as_0 = {33'b????0???????????????????????????0};
	      wildcard bins bit_27_wr_as_1 = {33'b????1???????????????????????????0};
	      wildcard bins bit_27_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_28_wr_as_0 = {33'b???0????????????????????????????0};
	      wildcard bins bit_28_wr_as_1 = {33'b???1????????????????????????????0};
	      wildcard bins bit_28_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_29_wr_as_0 = {33'b??0?????????????????????????????0};
	      wildcard bins bit_29_wr_as_1 = {33'b??1?????????????????????????????0};
	      wildcard bins bit_29_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_30_wr_as_0 = {33'b?0??????????????????????????????0};
	      wildcard bins bit_30_wr_as_1 = {33'b?1??????????????????????????????0};
	      wildcard bins bit_30_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_31_wr_as_0 = {33'b0???????????????????????????????0};
	      wildcard bins bit_31_wr_as_1 = {33'b1???????????????????????????????0};
	      wildcard bins bit_31_rd = {33'b????????????????????????????????1};
	      option.weight = 96;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCCSYN1");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_corr_syndromes_63_32 = uvm_reg_field::type_id::create("ecc_corr_syndromes_63_32",,get_full_name());
      this.ecc_corr_syndromes_63_32.configure(this, 32, 0, "RO", 0, 32'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCSYN1)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCSYN1
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCSYN2 extends uvm_reg;
	uvm_reg_field ecc_corr_syndromes_71_64;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_corr_syndromes_71_64: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {9'b???????00};
	      wildcard bins bit_0_wr_as_1 = {9'b???????10};
	      wildcard bins bit_0_rd = {9'b????????1};
	      wildcard bins bit_1_wr_as_0 = {9'b??????0?0};
	      wildcard bins bit_1_wr_as_1 = {9'b??????1?0};
	      wildcard bins bit_1_rd = {9'b????????1};
	      wildcard bins bit_2_wr_as_0 = {9'b?????0??0};
	      wildcard bins bit_2_wr_as_1 = {9'b?????1??0};
	      wildcard bins bit_2_rd = {9'b????????1};
	      wildcard bins bit_3_wr_as_0 = {9'b????0???0};
	      wildcard bins bit_3_wr_as_1 = {9'b????1???0};
	      wildcard bins bit_3_rd = {9'b????????1};
	      wildcard bins bit_4_wr_as_0 = {9'b???0????0};
	      wildcard bins bit_4_wr_as_1 = {9'b???1????0};
	      wildcard bins bit_4_rd = {9'b????????1};
	      wildcard bins bit_5_wr_as_0 = {9'b??0?????0};
	      wildcard bins bit_5_wr_as_1 = {9'b??1?????0};
	      wildcard bins bit_5_rd = {9'b????????1};
	      wildcard bins bit_6_wr_as_0 = {9'b?0??????0};
	      wildcard bins bit_6_wr_as_1 = {9'b?1??????0};
	      wildcard bins bit_6_rd = {9'b????????1};
	      wildcard bins bit_7_wr_as_0 = {9'b0???????0};
	      wildcard bins bit_7_wr_as_1 = {9'b1???????0};
	      wildcard bins bit_7_rd = {9'b????????1};
	      option.weight = 24;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCCSYN2");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_corr_syndromes_71_64 = uvm_reg_field::type_id::create("ecc_corr_syndromes_71_64",,get_full_name());
      this.ecc_corr_syndromes_71_64.configure(this, 8, 0, "RO", 0, 8'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCSYN2)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCSYN2
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCBITMASK0 extends uvm_reg;
	uvm_reg_field ecc_corr_bit_mask_31_0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_corr_bit_mask_31_0: coverpoint {m_data[31:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {33'b???????????????????????????????00};
	      wildcard bins bit_0_wr_as_1 = {33'b???????????????????????????????10};
	      wildcard bins bit_0_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_1_wr_as_0 = {33'b??????????????????????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {33'b??????????????????????????????1?0};
	      wildcard bins bit_1_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_2_wr_as_0 = {33'b?????????????????????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {33'b?????????????????????????????1??0};
	      wildcard bins bit_2_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_3_wr_as_0 = {33'b????????????????????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {33'b????????????????????????????1???0};
	      wildcard bins bit_3_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_4_wr_as_0 = {33'b???????????????????????????0????0};
	      wildcard bins bit_4_wr_as_1 = {33'b???????????????????????????1????0};
	      wildcard bins bit_4_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_5_wr_as_0 = {33'b??????????????????????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {33'b??????????????????????????1?????0};
	      wildcard bins bit_5_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_6_wr_as_0 = {33'b?????????????????????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {33'b?????????????????????????1??????0};
	      wildcard bins bit_6_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_7_wr_as_0 = {33'b????????????????????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {33'b????????????????????????1???????0};
	      wildcard bins bit_7_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_8_wr_as_0 = {33'b???????????????????????0????????0};
	      wildcard bins bit_8_wr_as_1 = {33'b???????????????????????1????????0};
	      wildcard bins bit_8_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_9_wr_as_0 = {33'b??????????????????????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {33'b??????????????????????1?????????0};
	      wildcard bins bit_9_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_10_wr_as_0 = {33'b?????????????????????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {33'b?????????????????????1??????????0};
	      wildcard bins bit_10_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_11_wr_as_0 = {33'b????????????????????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {33'b????????????????????1???????????0};
	      wildcard bins bit_11_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_12_wr_as_0 = {33'b???????????????????0????????????0};
	      wildcard bins bit_12_wr_as_1 = {33'b???????????????????1????????????0};
	      wildcard bins bit_12_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_13_wr_as_0 = {33'b??????????????????0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {33'b??????????????????1?????????????0};
	      wildcard bins bit_13_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_14_wr_as_0 = {33'b?????????????????0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {33'b?????????????????1??????????????0};
	      wildcard bins bit_14_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_15_wr_as_0 = {33'b????????????????0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {33'b????????????????1???????????????0};
	      wildcard bins bit_15_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_16_wr_as_0 = {33'b???????????????0????????????????0};
	      wildcard bins bit_16_wr_as_1 = {33'b???????????????1????????????????0};
	      wildcard bins bit_16_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_17_wr_as_0 = {33'b??????????????0?????????????????0};
	      wildcard bins bit_17_wr_as_1 = {33'b??????????????1?????????????????0};
	      wildcard bins bit_17_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_18_wr_as_0 = {33'b?????????????0??????????????????0};
	      wildcard bins bit_18_wr_as_1 = {33'b?????????????1??????????????????0};
	      wildcard bins bit_18_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_19_wr_as_0 = {33'b????????????0???????????????????0};
	      wildcard bins bit_19_wr_as_1 = {33'b????????????1???????????????????0};
	      wildcard bins bit_19_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_20_wr_as_0 = {33'b???????????0????????????????????0};
	      wildcard bins bit_20_wr_as_1 = {33'b???????????1????????????????????0};
	      wildcard bins bit_20_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_21_wr_as_0 = {33'b??????????0?????????????????????0};
	      wildcard bins bit_21_wr_as_1 = {33'b??????????1?????????????????????0};
	      wildcard bins bit_21_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_22_wr_as_0 = {33'b?????????0??????????????????????0};
	      wildcard bins bit_22_wr_as_1 = {33'b?????????1??????????????????????0};
	      wildcard bins bit_22_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_23_wr_as_0 = {33'b????????0???????????????????????0};
	      wildcard bins bit_23_wr_as_1 = {33'b????????1???????????????????????0};
	      wildcard bins bit_23_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_24_wr_as_0 = {33'b???????0????????????????????????0};
	      wildcard bins bit_24_wr_as_1 = {33'b???????1????????????????????????0};
	      wildcard bins bit_24_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_25_wr_as_0 = {33'b??????0?????????????????????????0};
	      wildcard bins bit_25_wr_as_1 = {33'b??????1?????????????????????????0};
	      wildcard bins bit_25_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_26_wr_as_0 = {33'b?????0??????????????????????????0};
	      wildcard bins bit_26_wr_as_1 = {33'b?????1??????????????????????????0};
	      wildcard bins bit_26_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_27_wr_as_0 = {33'b????0???????????????????????????0};
	      wildcard bins bit_27_wr_as_1 = {33'b????1???????????????????????????0};
	      wildcard bins bit_27_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_28_wr_as_0 = {33'b???0????????????????????????????0};
	      wildcard bins bit_28_wr_as_1 = {33'b???1????????????????????????????0};
	      wildcard bins bit_28_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_29_wr_as_0 = {33'b??0?????????????????????????????0};
	      wildcard bins bit_29_wr_as_1 = {33'b??1?????????????????????????????0};
	      wildcard bins bit_29_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_30_wr_as_0 = {33'b?0??????????????????????????????0};
	      wildcard bins bit_30_wr_as_1 = {33'b?1??????????????????????????????0};
	      wildcard bins bit_30_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_31_wr_as_0 = {33'b0???????????????????????????????0};
	      wildcard bins bit_31_wr_as_1 = {33'b1???????????????????????????????0};
	      wildcard bins bit_31_rd = {33'b????????????????????????????????1};
	      option.weight = 96;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCBITMASK0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_corr_bit_mask_31_0 = uvm_reg_field::type_id::create("ecc_corr_bit_mask_31_0",,get_full_name());
      this.ecc_corr_bit_mask_31_0.configure(this, 32, 0, "RO", 0, 32'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCBITMASK0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCBITMASK0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCBITMASK1 extends uvm_reg;
	uvm_reg_field ecc_corr_bit_mask_63_32;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_corr_bit_mask_63_32: coverpoint {m_data[31:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {33'b???????????????????????????????00};
	      wildcard bins bit_0_wr_as_1 = {33'b???????????????????????????????10};
	      wildcard bins bit_0_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_1_wr_as_0 = {33'b??????????????????????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {33'b??????????????????????????????1?0};
	      wildcard bins bit_1_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_2_wr_as_0 = {33'b?????????????????????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {33'b?????????????????????????????1??0};
	      wildcard bins bit_2_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_3_wr_as_0 = {33'b????????????????????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {33'b????????????????????????????1???0};
	      wildcard bins bit_3_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_4_wr_as_0 = {33'b???????????????????????????0????0};
	      wildcard bins bit_4_wr_as_1 = {33'b???????????????????????????1????0};
	      wildcard bins bit_4_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_5_wr_as_0 = {33'b??????????????????????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {33'b??????????????????????????1?????0};
	      wildcard bins bit_5_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_6_wr_as_0 = {33'b?????????????????????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {33'b?????????????????????????1??????0};
	      wildcard bins bit_6_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_7_wr_as_0 = {33'b????????????????????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {33'b????????????????????????1???????0};
	      wildcard bins bit_7_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_8_wr_as_0 = {33'b???????????????????????0????????0};
	      wildcard bins bit_8_wr_as_1 = {33'b???????????????????????1????????0};
	      wildcard bins bit_8_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_9_wr_as_0 = {33'b??????????????????????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {33'b??????????????????????1?????????0};
	      wildcard bins bit_9_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_10_wr_as_0 = {33'b?????????????????????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {33'b?????????????????????1??????????0};
	      wildcard bins bit_10_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_11_wr_as_0 = {33'b????????????????????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {33'b????????????????????1???????????0};
	      wildcard bins bit_11_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_12_wr_as_0 = {33'b???????????????????0????????????0};
	      wildcard bins bit_12_wr_as_1 = {33'b???????????????????1????????????0};
	      wildcard bins bit_12_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_13_wr_as_0 = {33'b??????????????????0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {33'b??????????????????1?????????????0};
	      wildcard bins bit_13_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_14_wr_as_0 = {33'b?????????????????0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {33'b?????????????????1??????????????0};
	      wildcard bins bit_14_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_15_wr_as_0 = {33'b????????????????0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {33'b????????????????1???????????????0};
	      wildcard bins bit_15_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_16_wr_as_0 = {33'b???????????????0????????????????0};
	      wildcard bins bit_16_wr_as_1 = {33'b???????????????1????????????????0};
	      wildcard bins bit_16_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_17_wr_as_0 = {33'b??????????????0?????????????????0};
	      wildcard bins bit_17_wr_as_1 = {33'b??????????????1?????????????????0};
	      wildcard bins bit_17_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_18_wr_as_0 = {33'b?????????????0??????????????????0};
	      wildcard bins bit_18_wr_as_1 = {33'b?????????????1??????????????????0};
	      wildcard bins bit_18_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_19_wr_as_0 = {33'b????????????0???????????????????0};
	      wildcard bins bit_19_wr_as_1 = {33'b????????????1???????????????????0};
	      wildcard bins bit_19_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_20_wr_as_0 = {33'b???????????0????????????????????0};
	      wildcard bins bit_20_wr_as_1 = {33'b???????????1????????????????????0};
	      wildcard bins bit_20_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_21_wr_as_0 = {33'b??????????0?????????????????????0};
	      wildcard bins bit_21_wr_as_1 = {33'b??????????1?????????????????????0};
	      wildcard bins bit_21_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_22_wr_as_0 = {33'b?????????0??????????????????????0};
	      wildcard bins bit_22_wr_as_1 = {33'b?????????1??????????????????????0};
	      wildcard bins bit_22_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_23_wr_as_0 = {33'b????????0???????????????????????0};
	      wildcard bins bit_23_wr_as_1 = {33'b????????1???????????????????????0};
	      wildcard bins bit_23_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_24_wr_as_0 = {33'b???????0????????????????????????0};
	      wildcard bins bit_24_wr_as_1 = {33'b???????1????????????????????????0};
	      wildcard bins bit_24_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_25_wr_as_0 = {33'b??????0?????????????????????????0};
	      wildcard bins bit_25_wr_as_1 = {33'b??????1?????????????????????????0};
	      wildcard bins bit_25_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_26_wr_as_0 = {33'b?????0??????????????????????????0};
	      wildcard bins bit_26_wr_as_1 = {33'b?????1??????????????????????????0};
	      wildcard bins bit_26_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_27_wr_as_0 = {33'b????0???????????????????????????0};
	      wildcard bins bit_27_wr_as_1 = {33'b????1???????????????????????????0};
	      wildcard bins bit_27_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_28_wr_as_0 = {33'b???0????????????????????????????0};
	      wildcard bins bit_28_wr_as_1 = {33'b???1????????????????????????????0};
	      wildcard bins bit_28_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_29_wr_as_0 = {33'b??0?????????????????????????????0};
	      wildcard bins bit_29_wr_as_1 = {33'b??1?????????????????????????????0};
	      wildcard bins bit_29_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_30_wr_as_0 = {33'b?0??????????????????????????????0};
	      wildcard bins bit_30_wr_as_1 = {33'b?1??????????????????????????????0};
	      wildcard bins bit_30_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_31_wr_as_0 = {33'b0???????????????????????????????0};
	      wildcard bins bit_31_wr_as_1 = {33'b1???????????????????????????????0};
	      wildcard bins bit_31_rd = {33'b????????????????????????????????1};
	      option.weight = 96;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCBITMASK1");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_corr_bit_mask_63_32 = uvm_reg_field::type_id::create("ecc_corr_bit_mask_63_32",,get_full_name());
      this.ecc_corr_bit_mask_63_32.configure(this, 32, 0, "RO", 0, 32'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCBITMASK1)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCBITMASK1
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCBITMASK2 extends uvm_reg;
	uvm_reg_field ecc_corr_bit_mask_71_64;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_corr_bit_mask_71_64: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {9'b???????00};
	      wildcard bins bit_0_wr_as_1 = {9'b???????10};
	      wildcard bins bit_0_rd = {9'b????????1};
	      wildcard bins bit_1_wr_as_0 = {9'b??????0?0};
	      wildcard bins bit_1_wr_as_1 = {9'b??????1?0};
	      wildcard bins bit_1_rd = {9'b????????1};
	      wildcard bins bit_2_wr_as_0 = {9'b?????0??0};
	      wildcard bins bit_2_wr_as_1 = {9'b?????1??0};
	      wildcard bins bit_2_rd = {9'b????????1};
	      wildcard bins bit_3_wr_as_0 = {9'b????0???0};
	      wildcard bins bit_3_wr_as_1 = {9'b????1???0};
	      wildcard bins bit_3_rd = {9'b????????1};
	      wildcard bins bit_4_wr_as_0 = {9'b???0????0};
	      wildcard bins bit_4_wr_as_1 = {9'b???1????0};
	      wildcard bins bit_4_rd = {9'b????????1};
	      wildcard bins bit_5_wr_as_0 = {9'b??0?????0};
	      wildcard bins bit_5_wr_as_1 = {9'b??1?????0};
	      wildcard bins bit_5_rd = {9'b????????1};
	      wildcard bins bit_6_wr_as_0 = {9'b?0??????0};
	      wildcard bins bit_6_wr_as_1 = {9'b?1??????0};
	      wildcard bins bit_6_rd = {9'b????????1};
	      wildcard bins bit_7_wr_as_0 = {9'b0???????0};
	      wildcard bins bit_7_wr_as_1 = {9'b1???????0};
	      wildcard bins bit_7_rd = {9'b????????1};
	      option.weight = 24;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCBITMASK2");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_corr_bit_mask_71_64 = uvm_reg_field::type_id::create("ecc_corr_bit_mask_71_64",,get_full_name());
      this.ecc_corr_bit_mask_71_64.configure(this, 8, 0, "RO", 0, 8'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCBITMASK2)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCBITMASK2
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUADDR0 extends uvm_reg;
	uvm_reg_field ecc_uncorr_row;
	uvm_reg_field ecc_uncorr_rank;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_uncorr_row: coverpoint {m_data[17:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {19'b?????????????????00};
	      wildcard bins bit_0_wr_as_1 = {19'b?????????????????10};
	      wildcard bins bit_0_rd = {19'b??????????????????1};
	      wildcard bins bit_1_wr_as_0 = {19'b????????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {19'b????????????????1?0};
	      wildcard bins bit_1_rd = {19'b??????????????????1};
	      wildcard bins bit_2_wr_as_0 = {19'b???????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {19'b???????????????1??0};
	      wildcard bins bit_2_rd = {19'b??????????????????1};
	      wildcard bins bit_3_wr_as_0 = {19'b??????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {19'b??????????????1???0};
	      wildcard bins bit_3_rd = {19'b??????????????????1};
	      wildcard bins bit_4_wr_as_0 = {19'b?????????????0????0};
	      wildcard bins bit_4_wr_as_1 = {19'b?????????????1????0};
	      wildcard bins bit_4_rd = {19'b??????????????????1};
	      wildcard bins bit_5_wr_as_0 = {19'b????????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {19'b????????????1?????0};
	      wildcard bins bit_5_rd = {19'b??????????????????1};
	      wildcard bins bit_6_wr_as_0 = {19'b???????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {19'b???????????1??????0};
	      wildcard bins bit_6_rd = {19'b??????????????????1};
	      wildcard bins bit_7_wr_as_0 = {19'b??????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {19'b??????????1???????0};
	      wildcard bins bit_7_rd = {19'b??????????????????1};
	      wildcard bins bit_8_wr_as_0 = {19'b?????????0????????0};
	      wildcard bins bit_8_wr_as_1 = {19'b?????????1????????0};
	      wildcard bins bit_8_rd = {19'b??????????????????1};
	      wildcard bins bit_9_wr_as_0 = {19'b????????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {19'b????????1?????????0};
	      wildcard bins bit_9_rd = {19'b??????????????????1};
	      wildcard bins bit_10_wr_as_0 = {19'b???????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {19'b???????1??????????0};
	      wildcard bins bit_10_rd = {19'b??????????????????1};
	      wildcard bins bit_11_wr_as_0 = {19'b??????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {19'b??????1???????????0};
	      wildcard bins bit_11_rd = {19'b??????????????????1};
	      wildcard bins bit_12_wr_as_0 = {19'b?????0????????????0};
	      wildcard bins bit_12_wr_as_1 = {19'b?????1????????????0};
	      wildcard bins bit_12_rd = {19'b??????????????????1};
	      wildcard bins bit_13_wr_as_0 = {19'b????0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {19'b????1?????????????0};
	      wildcard bins bit_13_rd = {19'b??????????????????1};
	      wildcard bins bit_14_wr_as_0 = {19'b???0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {19'b???1??????????????0};
	      wildcard bins bit_14_rd = {19'b??????????????????1};
	      wildcard bins bit_15_wr_as_0 = {19'b??0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {19'b??1???????????????0};
	      wildcard bins bit_15_rd = {19'b??????????????????1};
	      wildcard bins bit_16_wr_as_0 = {19'b?0????????????????0};
	      wildcard bins bit_16_wr_as_1 = {19'b?1????????????????0};
	      wildcard bins bit_16_rd = {19'b??????????????????1};
	      wildcard bins bit_17_wr_as_0 = {19'b0?????????????????0};
	      wildcard bins bit_17_wr_as_1 = {19'b1?????????????????0};
	      wildcard bins bit_17_rd = {19'b??????????????????1};
	      option.weight = 54;
	   }
	   ecc_uncorr_rank: coverpoint {m_data[24:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCUADDR0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_uncorr_row = uvm_reg_field::type_id::create("ecc_uncorr_row",,get_full_name());
      this.ecc_uncorr_row.configure(this, 18, 0, "RO", 0, 18'h0, 1, 0, 1);
      this.ecc_uncorr_rank = uvm_reg_field::type_id::create("ecc_uncorr_rank",,get_full_name());
      this.ecc_uncorr_rank.configure(this, 1, 24, "RO", 0, 1'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUADDR0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUADDR0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUADDR1 extends uvm_reg;
	uvm_reg_field ecc_uncorr_col;
	uvm_reg_field ecc_uncorr_bank;
	uvm_reg_field ecc_uncorr_bg;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_uncorr_col: coverpoint {m_data[10:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {12'b??????????00};
	      wildcard bins bit_0_wr_as_1 = {12'b??????????10};
	      wildcard bins bit_0_rd = {12'b???????????1};
	      wildcard bins bit_1_wr_as_0 = {12'b?????????0?0};
	      wildcard bins bit_1_wr_as_1 = {12'b?????????1?0};
	      wildcard bins bit_1_rd = {12'b???????????1};
	      wildcard bins bit_2_wr_as_0 = {12'b????????0??0};
	      wildcard bins bit_2_wr_as_1 = {12'b????????1??0};
	      wildcard bins bit_2_rd = {12'b???????????1};
	      wildcard bins bit_3_wr_as_0 = {12'b???????0???0};
	      wildcard bins bit_3_wr_as_1 = {12'b???????1???0};
	      wildcard bins bit_3_rd = {12'b???????????1};
	      wildcard bins bit_4_wr_as_0 = {12'b??????0????0};
	      wildcard bins bit_4_wr_as_1 = {12'b??????1????0};
	      wildcard bins bit_4_rd = {12'b???????????1};
	      wildcard bins bit_5_wr_as_0 = {12'b?????0?????0};
	      wildcard bins bit_5_wr_as_1 = {12'b?????1?????0};
	      wildcard bins bit_5_rd = {12'b???????????1};
	      wildcard bins bit_6_wr_as_0 = {12'b????0??????0};
	      wildcard bins bit_6_wr_as_1 = {12'b????1??????0};
	      wildcard bins bit_6_rd = {12'b???????????1};
	      wildcard bins bit_7_wr_as_0 = {12'b???0???????0};
	      wildcard bins bit_7_wr_as_1 = {12'b???1???????0};
	      wildcard bins bit_7_rd = {12'b???????????1};
	      wildcard bins bit_8_wr_as_0 = {12'b??0????????0};
	      wildcard bins bit_8_wr_as_1 = {12'b??1????????0};
	      wildcard bins bit_8_rd = {12'b???????????1};
	      wildcard bins bit_9_wr_as_0 = {12'b?0?????????0};
	      wildcard bins bit_9_wr_as_1 = {12'b?1?????????0};
	      wildcard bins bit_9_rd = {12'b???????????1};
	      wildcard bins bit_10_wr_as_0 = {12'b0??????????0};
	      wildcard bins bit_10_wr_as_1 = {12'b1??????????0};
	      wildcard bins bit_10_rd = {12'b???????????1};
	      option.weight = 33;
	   }
	   ecc_uncorr_bank: coverpoint {m_data[18:16], m_is_read} iff(m_be) {
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
	   ecc_uncorr_bg: coverpoint {m_data[25:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {3'b?00};
	      wildcard bins bit_0_wr_as_1 = {3'b?10};
	      wildcard bins bit_0_rd = {3'b??1};
	      wildcard bins bit_1_wr_as_0 = {3'b0?0};
	      wildcard bins bit_1_wr_as_1 = {3'b1?0};
	      wildcard bins bit_1_rd = {3'b??1};
	      option.weight = 6;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCUADDR1");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_uncorr_col = uvm_reg_field::type_id::create("ecc_uncorr_col",,get_full_name());
      this.ecc_uncorr_col.configure(this, 11, 0, "RO", 0, 11'h0, 1, 0, 1);
      this.ecc_uncorr_bank = uvm_reg_field::type_id::create("ecc_uncorr_bank",,get_full_name());
      this.ecc_uncorr_bank.configure(this, 3, 16, "RO", 0, 3'h0, 1, 0, 1);
      this.ecc_uncorr_bg = uvm_reg_field::type_id::create("ecc_uncorr_bg",,get_full_name());
      this.ecc_uncorr_bg.configure(this, 2, 24, "RO", 0, 2'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUADDR1)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUADDR1
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUSYN0 extends uvm_reg;
	uvm_reg_field ecc_uncorr_syndromes_31_0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_uncorr_syndromes_31_0: coverpoint {m_data[31:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {33'b???????????????????????????????00};
	      wildcard bins bit_0_wr_as_1 = {33'b???????????????????????????????10};
	      wildcard bins bit_0_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_1_wr_as_0 = {33'b??????????????????????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {33'b??????????????????????????????1?0};
	      wildcard bins bit_1_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_2_wr_as_0 = {33'b?????????????????????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {33'b?????????????????????????????1??0};
	      wildcard bins bit_2_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_3_wr_as_0 = {33'b????????????????????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {33'b????????????????????????????1???0};
	      wildcard bins bit_3_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_4_wr_as_0 = {33'b???????????????????????????0????0};
	      wildcard bins bit_4_wr_as_1 = {33'b???????????????????????????1????0};
	      wildcard bins bit_4_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_5_wr_as_0 = {33'b??????????????????????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {33'b??????????????????????????1?????0};
	      wildcard bins bit_5_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_6_wr_as_0 = {33'b?????????????????????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {33'b?????????????????????????1??????0};
	      wildcard bins bit_6_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_7_wr_as_0 = {33'b????????????????????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {33'b????????????????????????1???????0};
	      wildcard bins bit_7_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_8_wr_as_0 = {33'b???????????????????????0????????0};
	      wildcard bins bit_8_wr_as_1 = {33'b???????????????????????1????????0};
	      wildcard bins bit_8_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_9_wr_as_0 = {33'b??????????????????????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {33'b??????????????????????1?????????0};
	      wildcard bins bit_9_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_10_wr_as_0 = {33'b?????????????????????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {33'b?????????????????????1??????????0};
	      wildcard bins bit_10_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_11_wr_as_0 = {33'b????????????????????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {33'b????????????????????1???????????0};
	      wildcard bins bit_11_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_12_wr_as_0 = {33'b???????????????????0????????????0};
	      wildcard bins bit_12_wr_as_1 = {33'b???????????????????1????????????0};
	      wildcard bins bit_12_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_13_wr_as_0 = {33'b??????????????????0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {33'b??????????????????1?????????????0};
	      wildcard bins bit_13_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_14_wr_as_0 = {33'b?????????????????0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {33'b?????????????????1??????????????0};
	      wildcard bins bit_14_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_15_wr_as_0 = {33'b????????????????0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {33'b????????????????1???????????????0};
	      wildcard bins bit_15_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_16_wr_as_0 = {33'b???????????????0????????????????0};
	      wildcard bins bit_16_wr_as_1 = {33'b???????????????1????????????????0};
	      wildcard bins bit_16_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_17_wr_as_0 = {33'b??????????????0?????????????????0};
	      wildcard bins bit_17_wr_as_1 = {33'b??????????????1?????????????????0};
	      wildcard bins bit_17_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_18_wr_as_0 = {33'b?????????????0??????????????????0};
	      wildcard bins bit_18_wr_as_1 = {33'b?????????????1??????????????????0};
	      wildcard bins bit_18_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_19_wr_as_0 = {33'b????????????0???????????????????0};
	      wildcard bins bit_19_wr_as_1 = {33'b????????????1???????????????????0};
	      wildcard bins bit_19_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_20_wr_as_0 = {33'b???????????0????????????????????0};
	      wildcard bins bit_20_wr_as_1 = {33'b???????????1????????????????????0};
	      wildcard bins bit_20_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_21_wr_as_0 = {33'b??????????0?????????????????????0};
	      wildcard bins bit_21_wr_as_1 = {33'b??????????1?????????????????????0};
	      wildcard bins bit_21_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_22_wr_as_0 = {33'b?????????0??????????????????????0};
	      wildcard bins bit_22_wr_as_1 = {33'b?????????1??????????????????????0};
	      wildcard bins bit_22_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_23_wr_as_0 = {33'b????????0???????????????????????0};
	      wildcard bins bit_23_wr_as_1 = {33'b????????1???????????????????????0};
	      wildcard bins bit_23_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_24_wr_as_0 = {33'b???????0????????????????????????0};
	      wildcard bins bit_24_wr_as_1 = {33'b???????1????????????????????????0};
	      wildcard bins bit_24_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_25_wr_as_0 = {33'b??????0?????????????????????????0};
	      wildcard bins bit_25_wr_as_1 = {33'b??????1?????????????????????????0};
	      wildcard bins bit_25_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_26_wr_as_0 = {33'b?????0??????????????????????????0};
	      wildcard bins bit_26_wr_as_1 = {33'b?????1??????????????????????????0};
	      wildcard bins bit_26_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_27_wr_as_0 = {33'b????0???????????????????????????0};
	      wildcard bins bit_27_wr_as_1 = {33'b????1???????????????????????????0};
	      wildcard bins bit_27_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_28_wr_as_0 = {33'b???0????????????????????????????0};
	      wildcard bins bit_28_wr_as_1 = {33'b???1????????????????????????????0};
	      wildcard bins bit_28_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_29_wr_as_0 = {33'b??0?????????????????????????????0};
	      wildcard bins bit_29_wr_as_1 = {33'b??1?????????????????????????????0};
	      wildcard bins bit_29_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_30_wr_as_0 = {33'b?0??????????????????????????????0};
	      wildcard bins bit_30_wr_as_1 = {33'b?1??????????????????????????????0};
	      wildcard bins bit_30_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_31_wr_as_0 = {33'b0???????????????????????????????0};
	      wildcard bins bit_31_wr_as_1 = {33'b1???????????????????????????????0};
	      wildcard bins bit_31_rd = {33'b????????????????????????????????1};
	      option.weight = 96;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCUSYN0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_uncorr_syndromes_31_0 = uvm_reg_field::type_id::create("ecc_uncorr_syndromes_31_0",,get_full_name());
      this.ecc_uncorr_syndromes_31_0.configure(this, 32, 0, "RO", 0, 32'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUSYN0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUSYN0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUSYN1 extends uvm_reg;
	uvm_reg_field ecc_uncorr_syndromes_63_32;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_uncorr_syndromes_63_32: coverpoint {m_data[31:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {33'b???????????????????????????????00};
	      wildcard bins bit_0_wr_as_1 = {33'b???????????????????????????????10};
	      wildcard bins bit_0_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_1_wr_as_0 = {33'b??????????????????????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {33'b??????????????????????????????1?0};
	      wildcard bins bit_1_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_2_wr_as_0 = {33'b?????????????????????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {33'b?????????????????????????????1??0};
	      wildcard bins bit_2_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_3_wr_as_0 = {33'b????????????????????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {33'b????????????????????????????1???0};
	      wildcard bins bit_3_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_4_wr_as_0 = {33'b???????????????????????????0????0};
	      wildcard bins bit_4_wr_as_1 = {33'b???????????????????????????1????0};
	      wildcard bins bit_4_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_5_wr_as_0 = {33'b??????????????????????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {33'b??????????????????????????1?????0};
	      wildcard bins bit_5_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_6_wr_as_0 = {33'b?????????????????????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {33'b?????????????????????????1??????0};
	      wildcard bins bit_6_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_7_wr_as_0 = {33'b????????????????????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {33'b????????????????????????1???????0};
	      wildcard bins bit_7_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_8_wr_as_0 = {33'b???????????????????????0????????0};
	      wildcard bins bit_8_wr_as_1 = {33'b???????????????????????1????????0};
	      wildcard bins bit_8_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_9_wr_as_0 = {33'b??????????????????????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {33'b??????????????????????1?????????0};
	      wildcard bins bit_9_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_10_wr_as_0 = {33'b?????????????????????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {33'b?????????????????????1??????????0};
	      wildcard bins bit_10_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_11_wr_as_0 = {33'b????????????????????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {33'b????????????????????1???????????0};
	      wildcard bins bit_11_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_12_wr_as_0 = {33'b???????????????????0????????????0};
	      wildcard bins bit_12_wr_as_1 = {33'b???????????????????1????????????0};
	      wildcard bins bit_12_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_13_wr_as_0 = {33'b??????????????????0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {33'b??????????????????1?????????????0};
	      wildcard bins bit_13_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_14_wr_as_0 = {33'b?????????????????0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {33'b?????????????????1??????????????0};
	      wildcard bins bit_14_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_15_wr_as_0 = {33'b????????????????0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {33'b????????????????1???????????????0};
	      wildcard bins bit_15_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_16_wr_as_0 = {33'b???????????????0????????????????0};
	      wildcard bins bit_16_wr_as_1 = {33'b???????????????1????????????????0};
	      wildcard bins bit_16_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_17_wr_as_0 = {33'b??????????????0?????????????????0};
	      wildcard bins bit_17_wr_as_1 = {33'b??????????????1?????????????????0};
	      wildcard bins bit_17_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_18_wr_as_0 = {33'b?????????????0??????????????????0};
	      wildcard bins bit_18_wr_as_1 = {33'b?????????????1??????????????????0};
	      wildcard bins bit_18_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_19_wr_as_0 = {33'b????????????0???????????????????0};
	      wildcard bins bit_19_wr_as_1 = {33'b????????????1???????????????????0};
	      wildcard bins bit_19_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_20_wr_as_0 = {33'b???????????0????????????????????0};
	      wildcard bins bit_20_wr_as_1 = {33'b???????????1????????????????????0};
	      wildcard bins bit_20_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_21_wr_as_0 = {33'b??????????0?????????????????????0};
	      wildcard bins bit_21_wr_as_1 = {33'b??????????1?????????????????????0};
	      wildcard bins bit_21_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_22_wr_as_0 = {33'b?????????0??????????????????????0};
	      wildcard bins bit_22_wr_as_1 = {33'b?????????1??????????????????????0};
	      wildcard bins bit_22_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_23_wr_as_0 = {33'b????????0???????????????????????0};
	      wildcard bins bit_23_wr_as_1 = {33'b????????1???????????????????????0};
	      wildcard bins bit_23_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_24_wr_as_0 = {33'b???????0????????????????????????0};
	      wildcard bins bit_24_wr_as_1 = {33'b???????1????????????????????????0};
	      wildcard bins bit_24_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_25_wr_as_0 = {33'b??????0?????????????????????????0};
	      wildcard bins bit_25_wr_as_1 = {33'b??????1?????????????????????????0};
	      wildcard bins bit_25_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_26_wr_as_0 = {33'b?????0??????????????????????????0};
	      wildcard bins bit_26_wr_as_1 = {33'b?????1??????????????????????????0};
	      wildcard bins bit_26_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_27_wr_as_0 = {33'b????0???????????????????????????0};
	      wildcard bins bit_27_wr_as_1 = {33'b????1???????????????????????????0};
	      wildcard bins bit_27_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_28_wr_as_0 = {33'b???0????????????????????????????0};
	      wildcard bins bit_28_wr_as_1 = {33'b???1????????????????????????????0};
	      wildcard bins bit_28_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_29_wr_as_0 = {33'b??0?????????????????????????????0};
	      wildcard bins bit_29_wr_as_1 = {33'b??1?????????????????????????????0};
	      wildcard bins bit_29_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_30_wr_as_0 = {33'b?0??????????????????????????????0};
	      wildcard bins bit_30_wr_as_1 = {33'b?1??????????????????????????????0};
	      wildcard bins bit_30_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_31_wr_as_0 = {33'b0???????????????????????????????0};
	      wildcard bins bit_31_wr_as_1 = {33'b1???????????????????????????????0};
	      wildcard bins bit_31_rd = {33'b????????????????????????????????1};
	      option.weight = 96;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCUSYN1");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_uncorr_syndromes_63_32 = uvm_reg_field::type_id::create("ecc_uncorr_syndromes_63_32",,get_full_name());
      this.ecc_uncorr_syndromes_63_32.configure(this, 32, 0, "RO", 0, 32'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUSYN1)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUSYN1
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUSYN2 extends uvm_reg;
	uvm_reg_field ecc_uncorr_syndromes_71_64;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_uncorr_syndromes_71_64: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {9'b???????00};
	      wildcard bins bit_0_wr_as_1 = {9'b???????10};
	      wildcard bins bit_0_rd = {9'b????????1};
	      wildcard bins bit_1_wr_as_0 = {9'b??????0?0};
	      wildcard bins bit_1_wr_as_1 = {9'b??????1?0};
	      wildcard bins bit_1_rd = {9'b????????1};
	      wildcard bins bit_2_wr_as_0 = {9'b?????0??0};
	      wildcard bins bit_2_wr_as_1 = {9'b?????1??0};
	      wildcard bins bit_2_rd = {9'b????????1};
	      wildcard bins bit_3_wr_as_0 = {9'b????0???0};
	      wildcard bins bit_3_wr_as_1 = {9'b????1???0};
	      wildcard bins bit_3_rd = {9'b????????1};
	      wildcard bins bit_4_wr_as_0 = {9'b???0????0};
	      wildcard bins bit_4_wr_as_1 = {9'b???1????0};
	      wildcard bins bit_4_rd = {9'b????????1};
	      wildcard bins bit_5_wr_as_0 = {9'b??0?????0};
	      wildcard bins bit_5_wr_as_1 = {9'b??1?????0};
	      wildcard bins bit_5_rd = {9'b????????1};
	      wildcard bins bit_6_wr_as_0 = {9'b?0??????0};
	      wildcard bins bit_6_wr_as_1 = {9'b?1??????0};
	      wildcard bins bit_6_rd = {9'b????????1};
	      wildcard bins bit_7_wr_as_0 = {9'b0???????0};
	      wildcard bins bit_7_wr_as_1 = {9'b1???????0};
	      wildcard bins bit_7_rd = {9'b????????1};
	      option.weight = 24;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCUSYN2");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_uncorr_syndromes_71_64 = uvm_reg_field::type_id::create("ecc_uncorr_syndromes_71_64",,get_full_name());
      this.ecc_uncorr_syndromes_71_64.configure(this, 8, 0, "RO", 0, 8'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUSYN2)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUSYN2
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONADDR0 extends uvm_reg;
	rand uvm_reg_field ecc_poison_col;
	rand uvm_reg_field ecc_poison_rank;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_poison_col: coverpoint {m_data[11:0], m_is_read} iff(m_be) {
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
	   ecc_poison_rank: coverpoint {m_data[24:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONADDR0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_poison_col = uvm_reg_field::type_id::create("ecc_poison_col",,get_full_name());
      this.ecc_poison_col.configure(this, 12, 0, "RW", 1, 12'h0, 1, 0, 1);
      this.ecc_poison_rank = uvm_reg_field::type_id::create("ecc_poison_rank",,get_full_name());
      this.ecc_poison_rank.configure(this, 1, 24, "RW", 1, 1'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONADDR0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONADDR0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONADDR1 extends uvm_reg;
	rand uvm_reg_field ecc_poison_row;
	rand uvm_reg_field ecc_poison_bank;
	rand uvm_reg_field ecc_poison_bg;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_poison_row: coverpoint {m_data[17:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {19'b?????????????????00};
	      wildcard bins bit_0_wr_as_1 = {19'b?????????????????10};
	      wildcard bins bit_0_rd_as_0 = {19'b?????????????????01};
	      wildcard bins bit_0_rd_as_1 = {19'b?????????????????11};
	      wildcard bins bit_1_wr_as_0 = {19'b????????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {19'b????????????????1?0};
	      wildcard bins bit_1_rd_as_0 = {19'b????????????????0?1};
	      wildcard bins bit_1_rd_as_1 = {19'b????????????????1?1};
	      wildcard bins bit_2_wr_as_0 = {19'b???????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {19'b???????????????1??0};
	      wildcard bins bit_2_rd_as_0 = {19'b???????????????0??1};
	      wildcard bins bit_2_rd_as_1 = {19'b???????????????1??1};
	      wildcard bins bit_3_wr_as_0 = {19'b??????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {19'b??????????????1???0};
	      wildcard bins bit_3_rd_as_0 = {19'b??????????????0???1};
	      wildcard bins bit_3_rd_as_1 = {19'b??????????????1???1};
	      wildcard bins bit_4_wr_as_0 = {19'b?????????????0????0};
	      wildcard bins bit_4_wr_as_1 = {19'b?????????????1????0};
	      wildcard bins bit_4_rd_as_0 = {19'b?????????????0????1};
	      wildcard bins bit_4_rd_as_1 = {19'b?????????????1????1};
	      wildcard bins bit_5_wr_as_0 = {19'b????????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {19'b????????????1?????0};
	      wildcard bins bit_5_rd_as_0 = {19'b????????????0?????1};
	      wildcard bins bit_5_rd_as_1 = {19'b????????????1?????1};
	      wildcard bins bit_6_wr_as_0 = {19'b???????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {19'b???????????1??????0};
	      wildcard bins bit_6_rd_as_0 = {19'b???????????0??????1};
	      wildcard bins bit_6_rd_as_1 = {19'b???????????1??????1};
	      wildcard bins bit_7_wr_as_0 = {19'b??????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {19'b??????????1???????0};
	      wildcard bins bit_7_rd_as_0 = {19'b??????????0???????1};
	      wildcard bins bit_7_rd_as_1 = {19'b??????????1???????1};
	      wildcard bins bit_8_wr_as_0 = {19'b?????????0????????0};
	      wildcard bins bit_8_wr_as_1 = {19'b?????????1????????0};
	      wildcard bins bit_8_rd_as_0 = {19'b?????????0????????1};
	      wildcard bins bit_8_rd_as_1 = {19'b?????????1????????1};
	      wildcard bins bit_9_wr_as_0 = {19'b????????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {19'b????????1?????????0};
	      wildcard bins bit_9_rd_as_0 = {19'b????????0?????????1};
	      wildcard bins bit_9_rd_as_1 = {19'b????????1?????????1};
	      wildcard bins bit_10_wr_as_0 = {19'b???????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {19'b???????1??????????0};
	      wildcard bins bit_10_rd_as_0 = {19'b???????0??????????1};
	      wildcard bins bit_10_rd_as_1 = {19'b???????1??????????1};
	      wildcard bins bit_11_wr_as_0 = {19'b??????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {19'b??????1???????????0};
	      wildcard bins bit_11_rd_as_0 = {19'b??????0???????????1};
	      wildcard bins bit_11_rd_as_1 = {19'b??????1???????????1};
	      wildcard bins bit_12_wr_as_0 = {19'b?????0????????????0};
	      wildcard bins bit_12_wr_as_1 = {19'b?????1????????????0};
	      wildcard bins bit_12_rd_as_0 = {19'b?????0????????????1};
	      wildcard bins bit_12_rd_as_1 = {19'b?????1????????????1};
	      wildcard bins bit_13_wr_as_0 = {19'b????0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {19'b????1?????????????0};
	      wildcard bins bit_13_rd_as_0 = {19'b????0?????????????1};
	      wildcard bins bit_13_rd_as_1 = {19'b????1?????????????1};
	      wildcard bins bit_14_wr_as_0 = {19'b???0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {19'b???1??????????????0};
	      wildcard bins bit_14_rd_as_0 = {19'b???0??????????????1};
	      wildcard bins bit_14_rd_as_1 = {19'b???1??????????????1};
	      wildcard bins bit_15_wr_as_0 = {19'b??0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {19'b??1???????????????0};
	      wildcard bins bit_15_rd_as_0 = {19'b??0???????????????1};
	      wildcard bins bit_15_rd_as_1 = {19'b??1???????????????1};
	      wildcard bins bit_16_wr_as_0 = {19'b?0????????????????0};
	      wildcard bins bit_16_wr_as_1 = {19'b?1????????????????0};
	      wildcard bins bit_16_rd_as_0 = {19'b?0????????????????1};
	      wildcard bins bit_16_rd_as_1 = {19'b?1????????????????1};
	      wildcard bins bit_17_wr_as_0 = {19'b0?????????????????0};
	      wildcard bins bit_17_wr_as_1 = {19'b1?????????????????0};
	      wildcard bins bit_17_rd_as_0 = {19'b0?????????????????1};
	      wildcard bins bit_17_rd_as_1 = {19'b1?????????????????1};
	      option.weight = 72;
	   }
	   ecc_poison_bank: coverpoint {m_data[26:24], m_is_read} iff(m_be) {
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
	   ecc_poison_bg: coverpoint {m_data[29:28], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONADDR1");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_poison_row = uvm_reg_field::type_id::create("ecc_poison_row",,get_full_name());
      this.ecc_poison_row.configure(this, 18, 0, "RW", 1, 18'h0, 1, 0, 1);
      this.ecc_poison_bank = uvm_reg_field::type_id::create("ecc_poison_bank",,get_full_name());
      this.ecc_poison_bank.configure(this, 3, 24, "RW", 1, 3'h0, 1, 0, 0);
      this.ecc_poison_bg = uvm_reg_field::type_id::create("ecc_poison_bg",,get_full_name());
      this.ecc_poison_bg.configure(this, 2, 28, "RW", 1, 2'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONADDR1)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONADDR1
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONPAT0 extends uvm_reg;
	rand uvm_reg_field ecc_poison_data_31_0;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_poison_data_31_0: coverpoint {m_data[31:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONPAT0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_poison_data_31_0 = uvm_reg_field::type_id::create("ecc_poison_data_31_0",,get_full_name());
      this.ecc_poison_data_31_0.configure(this, 32, 0, "RW", 1, 32'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONPAT0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONPAT0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONPAT2 extends uvm_reg;
	rand uvm_reg_field ecc_poison_data_71_64;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_poison_data_71_64: coverpoint {m_data[7:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONPAT2");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_poison_data_71_64 = uvm_reg_field::type_id::create("ecc_poison_data_71_64",,get_full_name());
      this.ecc_poison_data_71_64.configure(this, 8, 0, "RW", 1, 8'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONPAT2)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONPAT2
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCAPSTAT extends uvm_reg;
	uvm_reg_field ecc_ap_err;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ecc_ap_err: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ECCAPSTAT");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ecc_ap_err = uvm_reg_field::type_id::create("ecc_ap_err",,get_full_name());
      this.ecc_ap_err.configure(this, 1, 0, "RO", 0, 1'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCAPSTAT)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCAPSTAT
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCCTL1 extends uvm_reg;
	rand uvm_reg_field rd_link_ecc_corr_intr_en;
	rand uvm_reg_field rd_link_ecc_corr_intr_clr;
	rand uvm_reg_field rd_link_ecc_corr_cnt_clr;
	rand uvm_reg_field rd_link_ecc_corr_intr_force;
	rand uvm_reg_field rd_link_ecc_uncorr_intr_en;
	rand uvm_reg_field rd_link_ecc_uncorr_intr_clr;
	rand uvm_reg_field rd_link_ecc_uncorr_cnt_clr;
	rand uvm_reg_field rd_link_ecc_uncorr_intr_force;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   rd_link_ecc_corr_intr_en: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   rd_link_ecc_corr_intr_clr: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   rd_link_ecc_corr_cnt_clr: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   rd_link_ecc_corr_intr_force: coverpoint {m_data[3:3], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   rd_link_ecc_uncorr_intr_en: coverpoint {m_data[4:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   rd_link_ecc_uncorr_intr_clr: coverpoint {m_data[5:5], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   rd_link_ecc_uncorr_cnt_clr: coverpoint {m_data[6:6], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   rd_link_ecc_uncorr_intr_force: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCCTL1");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.rd_link_ecc_corr_intr_en = uvm_reg_field::type_id::create("rd_link_ecc_corr_intr_en",,get_full_name());
      this.rd_link_ecc_corr_intr_en.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.rd_link_ecc_corr_intr_clr = uvm_reg_field::type_id::create("rd_link_ecc_corr_intr_clr",,get_full_name());
      this.rd_link_ecc_corr_intr_clr.configure(this, 1, 1, "W1C", 0, 1'h0, 1, 0, 0);
      this.rd_link_ecc_corr_cnt_clr = uvm_reg_field::type_id::create("rd_link_ecc_corr_cnt_clr",,get_full_name());
      this.rd_link_ecc_corr_cnt_clr.configure(this, 1, 2, "W1C", 0, 1'h0, 1, 0, 0);
      this.rd_link_ecc_corr_intr_force = uvm_reg_field::type_id::create("rd_link_ecc_corr_intr_force",,get_full_name());
      this.rd_link_ecc_corr_intr_force.configure(this, 1, 3, "W1C", 0, 1'h0, 1, 0, 0);
      this.rd_link_ecc_uncorr_intr_en = uvm_reg_field::type_id::create("rd_link_ecc_uncorr_intr_en",,get_full_name());
      this.rd_link_ecc_uncorr_intr_en.configure(this, 1, 4, "RW", 0, 1'h0, 1, 0, 0);
      this.rd_link_ecc_uncorr_intr_clr = uvm_reg_field::type_id::create("rd_link_ecc_uncorr_intr_clr",,get_full_name());
      this.rd_link_ecc_uncorr_intr_clr.configure(this, 1, 5, "W1C", 0, 1'h0, 1, 0, 0);
      this.rd_link_ecc_uncorr_cnt_clr = uvm_reg_field::type_id::create("rd_link_ecc_uncorr_cnt_clr",,get_full_name());
      this.rd_link_ecc_uncorr_cnt_clr.configure(this, 1, 6, "W1C", 0, 1'h0, 1, 0, 0);
      this.rd_link_ecc_uncorr_intr_force = uvm_reg_field::type_id::create("rd_link_ecc_uncorr_intr_force",,get_full_name());
      this.rd_link_ecc_uncorr_intr_force.configure(this, 1, 7, "W1C", 0, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCCTL1)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCCTL1
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCPOISONCTL0 extends uvm_reg;
	rand uvm_reg_field linkecc_poison_inject_en;
	rand uvm_reg_field linkecc_poison_type;
	rand uvm_reg_field linkecc_poison_rw;
	rand uvm_reg_field linkecc_poison_dmi_sel;
	rand uvm_reg_field linkecc_poison_byte_sel;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   linkecc_poison_inject_en: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   linkecc_poison_type: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   linkecc_poison_rw: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   linkecc_poison_dmi_sel: coverpoint {m_data[19:16], m_is_read} iff(m_be) {
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
	   linkecc_poison_byte_sel: coverpoint {m_data[27:24], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCPOISONCTL0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.linkecc_poison_inject_en = uvm_reg_field::type_id::create("linkecc_poison_inject_en",,get_full_name());
      this.linkecc_poison_inject_en.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.linkecc_poison_type = uvm_reg_field::type_id::create("linkecc_poison_type",,get_full_name());
      this.linkecc_poison_type.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
      this.linkecc_poison_rw = uvm_reg_field::type_id::create("linkecc_poison_rw",,get_full_name());
      this.linkecc_poison_rw.configure(this, 1, 2, "RW", 0, 1'h0, 1, 0, 0);
      this.linkecc_poison_dmi_sel = uvm_reg_field::type_id::create("linkecc_poison_dmi_sel",,get_full_name());
      this.linkecc_poison_dmi_sel.configure(this, 4, 16, "RW", 0, 4'h0, 1, 0, 1);
      this.linkecc_poison_byte_sel = uvm_reg_field::type_id::create("linkecc_poison_byte_sel",,get_full_name());
      this.linkecc_poison_byte_sel.configure(this, 4, 24, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCPOISONCTL0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCPOISONCTL0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCPOISONSTAT extends uvm_reg;
	uvm_reg_field linkecc_poison_complete;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   linkecc_poison_complete: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCPOISONSTAT");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.linkecc_poison_complete = uvm_reg_field::type_id::create("linkecc_poison_complete",,get_full_name());
      this.linkecc_poison_complete.configure(this, 1, 0, "RO", 0, 1'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCPOISONSTAT)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCPOISONSTAT
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCINDEX extends uvm_reg;
	rand uvm_reg_field rd_link_ecc_err_byte_sel;
	rand uvm_reg_field rd_link_ecc_err_rank_sel;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   rd_link_ecc_err_byte_sel: coverpoint {m_data[2:0], m_is_read} iff(m_be) {
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
	   rd_link_ecc_err_rank_sel: coverpoint {m_data[5:4], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCINDEX");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.rd_link_ecc_err_byte_sel = uvm_reg_field::type_id::create("rd_link_ecc_err_byte_sel",,get_full_name());
      this.rd_link_ecc_err_byte_sel.configure(this, 3, 0, "RW", 1, 3'h0, 1, 0, 0);
      this.rd_link_ecc_err_rank_sel = uvm_reg_field::type_id::create("rd_link_ecc_err_rank_sel",,get_full_name());
      this.rd_link_ecc_err_rank_sel.configure(this, 2, 4, "RW", 1, 2'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCINDEX)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCINDEX
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCERRCNT0 extends uvm_reg;
	uvm_reg_field rd_link_ecc_err_syndrome;
	uvm_reg_field rd_link_ecc_corr_cnt;
	uvm_reg_field rd_link_ecc_uncorr_cnt;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   rd_link_ecc_err_syndrome: coverpoint {m_data[8:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {10'b????????00};
	      wildcard bins bit_0_wr_as_1 = {10'b????????10};
	      wildcard bins bit_0_rd = {10'b?????????1};
	      wildcard bins bit_1_wr_as_0 = {10'b???????0?0};
	      wildcard bins bit_1_wr_as_1 = {10'b???????1?0};
	      wildcard bins bit_1_rd = {10'b?????????1};
	      wildcard bins bit_2_wr_as_0 = {10'b??????0??0};
	      wildcard bins bit_2_wr_as_1 = {10'b??????1??0};
	      wildcard bins bit_2_rd = {10'b?????????1};
	      wildcard bins bit_3_wr_as_0 = {10'b?????0???0};
	      wildcard bins bit_3_wr_as_1 = {10'b?????1???0};
	      wildcard bins bit_3_rd = {10'b?????????1};
	      wildcard bins bit_4_wr_as_0 = {10'b????0????0};
	      wildcard bins bit_4_wr_as_1 = {10'b????1????0};
	      wildcard bins bit_4_rd = {10'b?????????1};
	      wildcard bins bit_5_wr_as_0 = {10'b???0?????0};
	      wildcard bins bit_5_wr_as_1 = {10'b???1?????0};
	      wildcard bins bit_5_rd = {10'b?????????1};
	      wildcard bins bit_6_wr_as_0 = {10'b??0??????0};
	      wildcard bins bit_6_wr_as_1 = {10'b??1??????0};
	      wildcard bins bit_6_rd = {10'b?????????1};
	      wildcard bins bit_7_wr_as_0 = {10'b?0???????0};
	      wildcard bins bit_7_wr_as_1 = {10'b?1???????0};
	      wildcard bins bit_7_rd = {10'b?????????1};
	      wildcard bins bit_8_wr_as_0 = {10'b0????????0};
	      wildcard bins bit_8_wr_as_1 = {10'b1????????0};
	      wildcard bins bit_8_rd = {10'b?????????1};
	      option.weight = 27;
	   }
	   rd_link_ecc_corr_cnt: coverpoint {m_data[23:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {9'b???????00};
	      wildcard bins bit_0_wr_as_1 = {9'b???????10};
	      wildcard bins bit_0_rd = {9'b????????1};
	      wildcard bins bit_1_wr_as_0 = {9'b??????0?0};
	      wildcard bins bit_1_wr_as_1 = {9'b??????1?0};
	      wildcard bins bit_1_rd = {9'b????????1};
	      wildcard bins bit_2_wr_as_0 = {9'b?????0??0};
	      wildcard bins bit_2_wr_as_1 = {9'b?????1??0};
	      wildcard bins bit_2_rd = {9'b????????1};
	      wildcard bins bit_3_wr_as_0 = {9'b????0???0};
	      wildcard bins bit_3_wr_as_1 = {9'b????1???0};
	      wildcard bins bit_3_rd = {9'b????????1};
	      wildcard bins bit_4_wr_as_0 = {9'b???0????0};
	      wildcard bins bit_4_wr_as_1 = {9'b???1????0};
	      wildcard bins bit_4_rd = {9'b????????1};
	      wildcard bins bit_5_wr_as_0 = {9'b??0?????0};
	      wildcard bins bit_5_wr_as_1 = {9'b??1?????0};
	      wildcard bins bit_5_rd = {9'b????????1};
	      wildcard bins bit_6_wr_as_0 = {9'b?0??????0};
	      wildcard bins bit_6_wr_as_1 = {9'b?1??????0};
	      wildcard bins bit_6_rd = {9'b????????1};
	      wildcard bins bit_7_wr_as_0 = {9'b0???????0};
	      wildcard bins bit_7_wr_as_1 = {9'b1???????0};
	      wildcard bins bit_7_rd = {9'b????????1};
	      option.weight = 24;
	   }
	   rd_link_ecc_uncorr_cnt: coverpoint {m_data[31:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {9'b???????00};
	      wildcard bins bit_0_wr_as_1 = {9'b???????10};
	      wildcard bins bit_0_rd = {9'b????????1};
	      wildcard bins bit_1_wr_as_0 = {9'b??????0?0};
	      wildcard bins bit_1_wr_as_1 = {9'b??????1?0};
	      wildcard bins bit_1_rd = {9'b????????1};
	      wildcard bins bit_2_wr_as_0 = {9'b?????0??0};
	      wildcard bins bit_2_wr_as_1 = {9'b?????1??0};
	      wildcard bins bit_2_rd = {9'b????????1};
	      wildcard bins bit_3_wr_as_0 = {9'b????0???0};
	      wildcard bins bit_3_wr_as_1 = {9'b????1???0};
	      wildcard bins bit_3_rd = {9'b????????1};
	      wildcard bins bit_4_wr_as_0 = {9'b???0????0};
	      wildcard bins bit_4_wr_as_1 = {9'b???1????0};
	      wildcard bins bit_4_rd = {9'b????????1};
	      wildcard bins bit_5_wr_as_0 = {9'b??0?????0};
	      wildcard bins bit_5_wr_as_1 = {9'b??1?????0};
	      wildcard bins bit_5_rd = {9'b????????1};
	      wildcard bins bit_6_wr_as_0 = {9'b?0??????0};
	      wildcard bins bit_6_wr_as_1 = {9'b?1??????0};
	      wildcard bins bit_6_rd = {9'b????????1};
	      wildcard bins bit_7_wr_as_0 = {9'b0???????0};
	      wildcard bins bit_7_wr_as_1 = {9'b1???????0};
	      wildcard bins bit_7_rd = {9'b????????1};
	      option.weight = 24;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCERRCNT0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.rd_link_ecc_err_syndrome = uvm_reg_field::type_id::create("rd_link_ecc_err_syndrome",,get_full_name());
      this.rd_link_ecc_err_syndrome.configure(this, 9, 0, "RO", 0, 9'h0, 1, 0, 1);
      this.rd_link_ecc_corr_cnt = uvm_reg_field::type_id::create("rd_link_ecc_corr_cnt",,get_full_name());
      this.rd_link_ecc_corr_cnt.configure(this, 8, 16, "RO", 0, 8'h0, 1, 0, 1);
      this.rd_link_ecc_uncorr_cnt = uvm_reg_field::type_id::create("rd_link_ecc_uncorr_cnt",,get_full_name());
      this.rd_link_ecc_uncorr_cnt.configure(this, 8, 24, "RO", 0, 8'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCERRCNT0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCERRCNT0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCERRSTAT extends uvm_reg;
	uvm_reg_field rd_link_ecc_corr_err_int;
	uvm_reg_field rd_link_ecc_uncorr_err_int;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   rd_link_ecc_corr_err_int: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   rd_link_ecc_uncorr_err_int: coverpoint {m_data[11:8], m_is_read} iff(m_be) {
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
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCERRSTAT");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.rd_link_ecc_corr_err_int = uvm_reg_field::type_id::create("rd_link_ecc_corr_err_int",,get_full_name());
      this.rd_link_ecc_corr_err_int.configure(this, 4, 0, "RO", 0, 4'h0, 1, 0, 1);
      this.rd_link_ecc_uncorr_err_int = uvm_reg_field::type_id::create("rd_link_ecc_uncorr_err_int",,get_full_name());
      this.rd_link_ecc_uncorr_err_int.configure(this, 4, 8, "RO", 0, 4'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCERRSTAT)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCERRSTAT
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCCADDR0 extends uvm_reg;
	uvm_reg_field link_ecc_corr_row;
	uvm_reg_field link_ecc_corr_rank;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   link_ecc_corr_row: coverpoint {m_data[17:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {19'b?????????????????00};
	      wildcard bins bit_0_wr_as_1 = {19'b?????????????????10};
	      wildcard bins bit_0_rd = {19'b??????????????????1};
	      wildcard bins bit_1_wr_as_0 = {19'b????????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {19'b????????????????1?0};
	      wildcard bins bit_1_rd = {19'b??????????????????1};
	      wildcard bins bit_2_wr_as_0 = {19'b???????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {19'b???????????????1??0};
	      wildcard bins bit_2_rd = {19'b??????????????????1};
	      wildcard bins bit_3_wr_as_0 = {19'b??????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {19'b??????????????1???0};
	      wildcard bins bit_3_rd = {19'b??????????????????1};
	      wildcard bins bit_4_wr_as_0 = {19'b?????????????0????0};
	      wildcard bins bit_4_wr_as_1 = {19'b?????????????1????0};
	      wildcard bins bit_4_rd = {19'b??????????????????1};
	      wildcard bins bit_5_wr_as_0 = {19'b????????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {19'b????????????1?????0};
	      wildcard bins bit_5_rd = {19'b??????????????????1};
	      wildcard bins bit_6_wr_as_0 = {19'b???????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {19'b???????????1??????0};
	      wildcard bins bit_6_rd = {19'b??????????????????1};
	      wildcard bins bit_7_wr_as_0 = {19'b??????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {19'b??????????1???????0};
	      wildcard bins bit_7_rd = {19'b??????????????????1};
	      wildcard bins bit_8_wr_as_0 = {19'b?????????0????????0};
	      wildcard bins bit_8_wr_as_1 = {19'b?????????1????????0};
	      wildcard bins bit_8_rd = {19'b??????????????????1};
	      wildcard bins bit_9_wr_as_0 = {19'b????????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {19'b????????1?????????0};
	      wildcard bins bit_9_rd = {19'b??????????????????1};
	      wildcard bins bit_10_wr_as_0 = {19'b???????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {19'b???????1??????????0};
	      wildcard bins bit_10_rd = {19'b??????????????????1};
	      wildcard bins bit_11_wr_as_0 = {19'b??????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {19'b??????1???????????0};
	      wildcard bins bit_11_rd = {19'b??????????????????1};
	      wildcard bins bit_12_wr_as_0 = {19'b?????0????????????0};
	      wildcard bins bit_12_wr_as_1 = {19'b?????1????????????0};
	      wildcard bins bit_12_rd = {19'b??????????????????1};
	      wildcard bins bit_13_wr_as_0 = {19'b????0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {19'b????1?????????????0};
	      wildcard bins bit_13_rd = {19'b??????????????????1};
	      wildcard bins bit_14_wr_as_0 = {19'b???0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {19'b???1??????????????0};
	      wildcard bins bit_14_rd = {19'b??????????????????1};
	      wildcard bins bit_15_wr_as_0 = {19'b??0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {19'b??1???????????????0};
	      wildcard bins bit_15_rd = {19'b??????????????????1};
	      wildcard bins bit_16_wr_as_0 = {19'b?0????????????????0};
	      wildcard bins bit_16_wr_as_1 = {19'b?1????????????????0};
	      wildcard bins bit_16_rd = {19'b??????????????????1};
	      wildcard bins bit_17_wr_as_0 = {19'b0?????????????????0};
	      wildcard bins bit_17_wr_as_1 = {19'b1?????????????????0};
	      wildcard bins bit_17_rd = {19'b??????????????????1};
	      option.weight = 54;
	   }
	   link_ecc_corr_rank: coverpoint {m_data[24:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCCADDR0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.link_ecc_corr_row = uvm_reg_field::type_id::create("link_ecc_corr_row",,get_full_name());
      this.link_ecc_corr_row.configure(this, 18, 0, "RO", 1, 18'h0, 1, 0, 1);
      this.link_ecc_corr_rank = uvm_reg_field::type_id::create("link_ecc_corr_rank",,get_full_name());
      this.link_ecc_corr_rank.configure(this, 1, 24, "RO", 1, 1'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCCADDR0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCCADDR0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCCADDR1 extends uvm_reg;
	uvm_reg_field link_ecc_corr_col;
	uvm_reg_field link_ecc_corr_bank;
	uvm_reg_field link_ecc_corr_bg;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   link_ecc_corr_col: coverpoint {m_data[10:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {12'b??????????00};
	      wildcard bins bit_0_wr_as_1 = {12'b??????????10};
	      wildcard bins bit_0_rd = {12'b???????????1};
	      wildcard bins bit_1_wr_as_0 = {12'b?????????0?0};
	      wildcard bins bit_1_wr_as_1 = {12'b?????????1?0};
	      wildcard bins bit_1_rd = {12'b???????????1};
	      wildcard bins bit_2_wr_as_0 = {12'b????????0??0};
	      wildcard bins bit_2_wr_as_1 = {12'b????????1??0};
	      wildcard bins bit_2_rd = {12'b???????????1};
	      wildcard bins bit_3_wr_as_0 = {12'b???????0???0};
	      wildcard bins bit_3_wr_as_1 = {12'b???????1???0};
	      wildcard bins bit_3_rd = {12'b???????????1};
	      wildcard bins bit_4_wr_as_0 = {12'b??????0????0};
	      wildcard bins bit_4_wr_as_1 = {12'b??????1????0};
	      wildcard bins bit_4_rd = {12'b???????????1};
	      wildcard bins bit_5_wr_as_0 = {12'b?????0?????0};
	      wildcard bins bit_5_wr_as_1 = {12'b?????1?????0};
	      wildcard bins bit_5_rd = {12'b???????????1};
	      wildcard bins bit_6_wr_as_0 = {12'b????0??????0};
	      wildcard bins bit_6_wr_as_1 = {12'b????1??????0};
	      wildcard bins bit_6_rd = {12'b???????????1};
	      wildcard bins bit_7_wr_as_0 = {12'b???0???????0};
	      wildcard bins bit_7_wr_as_1 = {12'b???1???????0};
	      wildcard bins bit_7_rd = {12'b???????????1};
	      wildcard bins bit_8_wr_as_0 = {12'b??0????????0};
	      wildcard bins bit_8_wr_as_1 = {12'b??1????????0};
	      wildcard bins bit_8_rd = {12'b???????????1};
	      wildcard bins bit_9_wr_as_0 = {12'b?0?????????0};
	      wildcard bins bit_9_wr_as_1 = {12'b?1?????????0};
	      wildcard bins bit_9_rd = {12'b???????????1};
	      wildcard bins bit_10_wr_as_0 = {12'b0??????????0};
	      wildcard bins bit_10_wr_as_1 = {12'b1??????????0};
	      wildcard bins bit_10_rd = {12'b???????????1};
	      option.weight = 33;
	   }
	   link_ecc_corr_bank: coverpoint {m_data[18:16], m_is_read} iff(m_be) {
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
	   link_ecc_corr_bg: coverpoint {m_data[25:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {3'b?00};
	      wildcard bins bit_0_wr_as_1 = {3'b?10};
	      wildcard bins bit_0_rd = {3'b??1};
	      wildcard bins bit_1_wr_as_0 = {3'b0?0};
	      wildcard bins bit_1_wr_as_1 = {3'b1?0};
	      wildcard bins bit_1_rd = {3'b??1};
	      option.weight = 6;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCCADDR1");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.link_ecc_corr_col = uvm_reg_field::type_id::create("link_ecc_corr_col",,get_full_name());
      this.link_ecc_corr_col.configure(this, 11, 0, "RO", 1, 11'h0, 1, 0, 1);
      this.link_ecc_corr_bank = uvm_reg_field::type_id::create("link_ecc_corr_bank",,get_full_name());
      this.link_ecc_corr_bank.configure(this, 3, 16, "RO", 1, 3'h0, 1, 0, 1);
      this.link_ecc_corr_bg = uvm_reg_field::type_id::create("link_ecc_corr_bg",,get_full_name());
      this.link_ecc_corr_bg.configure(this, 2, 24, "RO", 1, 2'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCCADDR1)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCCADDR1
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCUADDR0 extends uvm_reg;
	uvm_reg_field link_ecc_uncorr_row;
	uvm_reg_field link_ecc_uncorr_rank;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   link_ecc_uncorr_row: coverpoint {m_data[17:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {19'b?????????????????00};
	      wildcard bins bit_0_wr_as_1 = {19'b?????????????????10};
	      wildcard bins bit_0_rd = {19'b??????????????????1};
	      wildcard bins bit_1_wr_as_0 = {19'b????????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {19'b????????????????1?0};
	      wildcard bins bit_1_rd = {19'b??????????????????1};
	      wildcard bins bit_2_wr_as_0 = {19'b???????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {19'b???????????????1??0};
	      wildcard bins bit_2_rd = {19'b??????????????????1};
	      wildcard bins bit_3_wr_as_0 = {19'b??????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {19'b??????????????1???0};
	      wildcard bins bit_3_rd = {19'b??????????????????1};
	      wildcard bins bit_4_wr_as_0 = {19'b?????????????0????0};
	      wildcard bins bit_4_wr_as_1 = {19'b?????????????1????0};
	      wildcard bins bit_4_rd = {19'b??????????????????1};
	      wildcard bins bit_5_wr_as_0 = {19'b????????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {19'b????????????1?????0};
	      wildcard bins bit_5_rd = {19'b??????????????????1};
	      wildcard bins bit_6_wr_as_0 = {19'b???????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {19'b???????????1??????0};
	      wildcard bins bit_6_rd = {19'b??????????????????1};
	      wildcard bins bit_7_wr_as_0 = {19'b??????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {19'b??????????1???????0};
	      wildcard bins bit_7_rd = {19'b??????????????????1};
	      wildcard bins bit_8_wr_as_0 = {19'b?????????0????????0};
	      wildcard bins bit_8_wr_as_1 = {19'b?????????1????????0};
	      wildcard bins bit_8_rd = {19'b??????????????????1};
	      wildcard bins bit_9_wr_as_0 = {19'b????????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {19'b????????1?????????0};
	      wildcard bins bit_9_rd = {19'b??????????????????1};
	      wildcard bins bit_10_wr_as_0 = {19'b???????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {19'b???????1??????????0};
	      wildcard bins bit_10_rd = {19'b??????????????????1};
	      wildcard bins bit_11_wr_as_0 = {19'b??????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {19'b??????1???????????0};
	      wildcard bins bit_11_rd = {19'b??????????????????1};
	      wildcard bins bit_12_wr_as_0 = {19'b?????0????????????0};
	      wildcard bins bit_12_wr_as_1 = {19'b?????1????????????0};
	      wildcard bins bit_12_rd = {19'b??????????????????1};
	      wildcard bins bit_13_wr_as_0 = {19'b????0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {19'b????1?????????????0};
	      wildcard bins bit_13_rd = {19'b??????????????????1};
	      wildcard bins bit_14_wr_as_0 = {19'b???0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {19'b???1??????????????0};
	      wildcard bins bit_14_rd = {19'b??????????????????1};
	      wildcard bins bit_15_wr_as_0 = {19'b??0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {19'b??1???????????????0};
	      wildcard bins bit_15_rd = {19'b??????????????????1};
	      wildcard bins bit_16_wr_as_0 = {19'b?0????????????????0};
	      wildcard bins bit_16_wr_as_1 = {19'b?1????????????????0};
	      wildcard bins bit_16_rd = {19'b??????????????????1};
	      wildcard bins bit_17_wr_as_0 = {19'b0?????????????????0};
	      wildcard bins bit_17_wr_as_1 = {19'b1?????????????????0};
	      wildcard bins bit_17_rd = {19'b??????????????????1};
	      option.weight = 54;
	   }
	   link_ecc_uncorr_rank: coverpoint {m_data[24:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCUADDR0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.link_ecc_uncorr_row = uvm_reg_field::type_id::create("link_ecc_uncorr_row",,get_full_name());
      this.link_ecc_uncorr_row.configure(this, 18, 0, "RO", 1, 18'h0, 1, 0, 1);
      this.link_ecc_uncorr_rank = uvm_reg_field::type_id::create("link_ecc_uncorr_rank",,get_full_name());
      this.link_ecc_uncorr_rank.configure(this, 1, 24, "RO", 1, 1'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCUADDR0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCUADDR0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCUADDR1 extends uvm_reg;
	uvm_reg_field link_ecc_uncorr_col;
	uvm_reg_field link_ecc_uncorr_bank;
	uvm_reg_field link_ecc_uncorr_bg;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   link_ecc_uncorr_col: coverpoint {m_data[10:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {12'b??????????00};
	      wildcard bins bit_0_wr_as_1 = {12'b??????????10};
	      wildcard bins bit_0_rd = {12'b???????????1};
	      wildcard bins bit_1_wr_as_0 = {12'b?????????0?0};
	      wildcard bins bit_1_wr_as_1 = {12'b?????????1?0};
	      wildcard bins bit_1_rd = {12'b???????????1};
	      wildcard bins bit_2_wr_as_0 = {12'b????????0??0};
	      wildcard bins bit_2_wr_as_1 = {12'b????????1??0};
	      wildcard bins bit_2_rd = {12'b???????????1};
	      wildcard bins bit_3_wr_as_0 = {12'b???????0???0};
	      wildcard bins bit_3_wr_as_1 = {12'b???????1???0};
	      wildcard bins bit_3_rd = {12'b???????????1};
	      wildcard bins bit_4_wr_as_0 = {12'b??????0????0};
	      wildcard bins bit_4_wr_as_1 = {12'b??????1????0};
	      wildcard bins bit_4_rd = {12'b???????????1};
	      wildcard bins bit_5_wr_as_0 = {12'b?????0?????0};
	      wildcard bins bit_5_wr_as_1 = {12'b?????1?????0};
	      wildcard bins bit_5_rd = {12'b???????????1};
	      wildcard bins bit_6_wr_as_0 = {12'b????0??????0};
	      wildcard bins bit_6_wr_as_1 = {12'b????1??????0};
	      wildcard bins bit_6_rd = {12'b???????????1};
	      wildcard bins bit_7_wr_as_0 = {12'b???0???????0};
	      wildcard bins bit_7_wr_as_1 = {12'b???1???????0};
	      wildcard bins bit_7_rd = {12'b???????????1};
	      wildcard bins bit_8_wr_as_0 = {12'b??0????????0};
	      wildcard bins bit_8_wr_as_1 = {12'b??1????????0};
	      wildcard bins bit_8_rd = {12'b???????????1};
	      wildcard bins bit_9_wr_as_0 = {12'b?0?????????0};
	      wildcard bins bit_9_wr_as_1 = {12'b?1?????????0};
	      wildcard bins bit_9_rd = {12'b???????????1};
	      wildcard bins bit_10_wr_as_0 = {12'b0??????????0};
	      wildcard bins bit_10_wr_as_1 = {12'b1??????????0};
	      wildcard bins bit_10_rd = {12'b???????????1};
	      option.weight = 33;
	   }
	   link_ecc_uncorr_bank: coverpoint {m_data[18:16], m_is_read} iff(m_be) {
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
	   link_ecc_uncorr_bg: coverpoint {m_data[25:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {3'b?00};
	      wildcard bins bit_0_wr_as_1 = {3'b?10};
	      wildcard bins bit_0_rd = {3'b??1};
	      wildcard bins bit_1_wr_as_0 = {3'b0?0};
	      wildcard bins bit_1_wr_as_1 = {3'b1?0};
	      wildcard bins bit_1_rd = {3'b??1};
	      option.weight = 6;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCUADDR1");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.link_ecc_uncorr_col = uvm_reg_field::type_id::create("link_ecc_uncorr_col",,get_full_name());
      this.link_ecc_uncorr_col.configure(this, 11, 0, "RO", 1, 11'h0, 1, 0, 1);
      this.link_ecc_uncorr_bank = uvm_reg_field::type_id::create("link_ecc_uncorr_bank",,get_full_name());
      this.link_ecc_uncorr_bank.configure(this, 3, 16, "RO", 1, 3'h0, 1, 0, 1);
      this.link_ecc_uncorr_bg = uvm_reg_field::type_id::create("link_ecc_uncorr_bg",,get_full_name());
      this.link_ecc_uncorr_bg.configure(this, 2, 24, "RO", 1, 2'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCUADDR1)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCUADDR1
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRL0 extends uvm_reg;
	rand uvm_reg_field dis_wc;
	rand uvm_reg_field dis_max_rank_rd_opt;
	rand uvm_reg_field dis_max_rank_wr_opt;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dis_wc: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dis_max_rank_rd_opt: coverpoint {m_data[6:6], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dis_max_rank_wr_opt: coverpoint {m_data[7:7], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRL0");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dis_wc = uvm_reg_field::type_id::create("dis_wc",,get_full_name());
      this.dis_wc.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.dis_max_rank_rd_opt = uvm_reg_field::type_id::create("dis_max_rank_rd_opt",,get_full_name());
      this.dis_max_rank_rd_opt.configure(this, 1, 6, "RW", 1, 1'h0, 1, 0, 0);
      this.dis_max_rank_wr_opt = uvm_reg_field::type_id::create("dis_max_rank_wr_opt",,get_full_name());
      this.dis_max_rank_wr_opt.configure(this, 1, 7, "RW", 1, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRL0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRL0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRL1 extends uvm_reg;
	rand uvm_reg_field dis_dq;
	rand uvm_reg_field dis_hif;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dis_dq: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   dis_hif: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRL1");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dis_dq = uvm_reg_field::type_id::create("dis_dq",,get_full_name());
      this.dis_dq.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.dis_hif = uvm_reg_field::type_id::create("dis_hif",,get_full_name());
      this.dis_hif.configure(this, 1, 1, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRL1)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRL1
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLCAM extends uvm_reg;
	uvm_reg_field dbg_hpr_q_depth;
	uvm_reg_field dbg_lpr_q_depth;
	uvm_reg_field dbg_w_q_depth;
	uvm_reg_field dbg_stall;
	uvm_reg_field dbg_rd_q_empty;
	uvm_reg_field dbg_wr_q_empty;
	uvm_reg_field rd_data_pipeline_empty;
	uvm_reg_field wr_data_pipeline_empty;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dbg_hpr_q_depth: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {8'b??????00};
	      wildcard bins bit_0_wr_as_1 = {8'b??????10};
	      wildcard bins bit_0_rd = {8'b???????1};
	      wildcard bins bit_1_wr_as_0 = {8'b?????0?0};
	      wildcard bins bit_1_wr_as_1 = {8'b?????1?0};
	      wildcard bins bit_1_rd = {8'b???????1};
	      wildcard bins bit_2_wr_as_0 = {8'b????0??0};
	      wildcard bins bit_2_wr_as_1 = {8'b????1??0};
	      wildcard bins bit_2_rd = {8'b???????1};
	      wildcard bins bit_3_wr_as_0 = {8'b???0???0};
	      wildcard bins bit_3_wr_as_1 = {8'b???1???0};
	      wildcard bins bit_3_rd = {8'b???????1};
	      wildcard bins bit_4_wr_as_0 = {8'b??0????0};
	      wildcard bins bit_4_wr_as_1 = {8'b??1????0};
	      wildcard bins bit_4_rd = {8'b???????1};
	      wildcard bins bit_5_wr_as_0 = {8'b?0?????0};
	      wildcard bins bit_5_wr_as_1 = {8'b?1?????0};
	      wildcard bins bit_5_rd = {8'b???????1};
	      wildcard bins bit_6_wr_as_0 = {8'b0??????0};
	      wildcard bins bit_6_wr_as_1 = {8'b1??????0};
	      wildcard bins bit_6_rd = {8'b???????1};
	      option.weight = 21;
	   }
	   dbg_lpr_q_depth: coverpoint {m_data[14:8], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {8'b??????00};
	      wildcard bins bit_0_wr_as_1 = {8'b??????10};
	      wildcard bins bit_0_rd = {8'b???????1};
	      wildcard bins bit_1_wr_as_0 = {8'b?????0?0};
	      wildcard bins bit_1_wr_as_1 = {8'b?????1?0};
	      wildcard bins bit_1_rd = {8'b???????1};
	      wildcard bins bit_2_wr_as_0 = {8'b????0??0};
	      wildcard bins bit_2_wr_as_1 = {8'b????1??0};
	      wildcard bins bit_2_rd = {8'b???????1};
	      wildcard bins bit_3_wr_as_0 = {8'b???0???0};
	      wildcard bins bit_3_wr_as_1 = {8'b???1???0};
	      wildcard bins bit_3_rd = {8'b???????1};
	      wildcard bins bit_4_wr_as_0 = {8'b??0????0};
	      wildcard bins bit_4_wr_as_1 = {8'b??1????0};
	      wildcard bins bit_4_rd = {8'b???????1};
	      wildcard bins bit_5_wr_as_0 = {8'b?0?????0};
	      wildcard bins bit_5_wr_as_1 = {8'b?1?????0};
	      wildcard bins bit_5_rd = {8'b???????1};
	      wildcard bins bit_6_wr_as_0 = {8'b0??????0};
	      wildcard bins bit_6_wr_as_1 = {8'b1??????0};
	      wildcard bins bit_6_rd = {8'b???????1};
	      option.weight = 21;
	   }
	   dbg_w_q_depth: coverpoint {m_data[22:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {8'b??????00};
	      wildcard bins bit_0_wr_as_1 = {8'b??????10};
	      wildcard bins bit_0_rd = {8'b???????1};
	      wildcard bins bit_1_wr_as_0 = {8'b?????0?0};
	      wildcard bins bit_1_wr_as_1 = {8'b?????1?0};
	      wildcard bins bit_1_rd = {8'b???????1};
	      wildcard bins bit_2_wr_as_0 = {8'b????0??0};
	      wildcard bins bit_2_wr_as_1 = {8'b????1??0};
	      wildcard bins bit_2_rd = {8'b???????1};
	      wildcard bins bit_3_wr_as_0 = {8'b???0???0};
	      wildcard bins bit_3_wr_as_1 = {8'b???1???0};
	      wildcard bins bit_3_rd = {8'b???????1};
	      wildcard bins bit_4_wr_as_0 = {8'b??0????0};
	      wildcard bins bit_4_wr_as_1 = {8'b??1????0};
	      wildcard bins bit_4_rd = {8'b???????1};
	      wildcard bins bit_5_wr_as_0 = {8'b?0?????0};
	      wildcard bins bit_5_wr_as_1 = {8'b?1?????0};
	      wildcard bins bit_5_rd = {8'b???????1};
	      wildcard bins bit_6_wr_as_0 = {8'b0??????0};
	      wildcard bins bit_6_wr_as_1 = {8'b1??????0};
	      wildcard bins bit_6_rd = {8'b???????1};
	      option.weight = 21;
	   }
	   dbg_stall: coverpoint {m_data[24:24], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   dbg_rd_q_empty: coverpoint {m_data[25:25], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   dbg_wr_q_empty: coverpoint {m_data[26:26], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   rd_data_pipeline_empty: coverpoint {m_data[28:28], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   wr_data_pipeline_empty: coverpoint {m_data[29:29], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLCAM");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dbg_hpr_q_depth = uvm_reg_field::type_id::create("dbg_hpr_q_depth",,get_full_name());
      this.dbg_hpr_q_depth.configure(this, 7, 0, "RO", 0, 7'h0, 1, 0, 1);
      this.dbg_lpr_q_depth = uvm_reg_field::type_id::create("dbg_lpr_q_depth",,get_full_name());
      this.dbg_lpr_q_depth.configure(this, 7, 8, "RO", 0, 7'h0, 1, 0, 1);
      this.dbg_w_q_depth = uvm_reg_field::type_id::create("dbg_w_q_depth",,get_full_name());
      this.dbg_w_q_depth.configure(this, 7, 16, "RO", 0, 7'h0, 1, 0, 1);
      this.dbg_stall = uvm_reg_field::type_id::create("dbg_stall",,get_full_name());
      this.dbg_stall.configure(this, 1, 24, "RO", 0, 1'h0, 1, 0, 0);
      this.dbg_rd_q_empty = uvm_reg_field::type_id::create("dbg_rd_q_empty",,get_full_name());
      this.dbg_rd_q_empty.configure(this, 1, 25, "RO", 1, 1'h0, 1, 0, 0);
      this.dbg_wr_q_empty = uvm_reg_field::type_id::create("dbg_wr_q_empty",,get_full_name());
      this.dbg_wr_q_empty.configure(this, 1, 26, "RO", 1, 1'h0, 1, 0, 0);
      this.rd_data_pipeline_empty = uvm_reg_field::type_id::create("rd_data_pipeline_empty",,get_full_name());
      this.rd_data_pipeline_empty.configure(this, 1, 28, "RO", 1, 1'h0, 1, 0, 0);
      this.wr_data_pipeline_empty = uvm_reg_field::type_id::create("wr_data_pipeline_empty",,get_full_name());
      this.wr_data_pipeline_empty.configure(this, 1, 29, "RO", 1, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLCAM)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLCAM
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLCMD extends uvm_reg;
	rand uvm_reg_field zq_calib_short;
	rand uvm_reg_field ctrlupd;
	rand uvm_reg_field ctrlupd_burst;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   zq_calib_short: coverpoint {m_data[16:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ctrlupd: coverpoint {m_data[17:17], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ctrlupd_burst: coverpoint {m_data[18:18], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLCMD");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.zq_calib_short = uvm_reg_field::type_id::create("zq_calib_short",,get_full_name());
      this.zq_calib_short.configure(this, 1, 16, "W1S", 0, 1'h0, 1, 0, 0);
      this.ctrlupd = uvm_reg_field::type_id::create("ctrlupd",,get_full_name());
      this.ctrlupd.configure(this, 1, 17, "W1S", 0, 1'h0, 1, 0, 0);
      this.ctrlupd_burst = uvm_reg_field::type_id::create("ctrlupd_burst",,get_full_name());
      this.ctrlupd_burst.configure(this, 1, 18, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLCMD)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLCMD
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLSTAT extends uvm_reg;
	uvm_reg_field zq_calib_short_busy;
	uvm_reg_field ctrlupd_busy;
	uvm_reg_field ctrlupd_burst_busy;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   zq_calib_short_busy: coverpoint {m_data[16:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   ctrlupd_busy: coverpoint {m_data[17:17], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   ctrlupd_burst_busy: coverpoint {m_data[18:18], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLSTAT");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.zq_calib_short_busy = uvm_reg_field::type_id::create("zq_calib_short_busy",,get_full_name());
      this.zq_calib_short_busy.configure(this, 1, 16, "RO", 0, 1'h0, 1, 0, 0);
      this.ctrlupd_busy = uvm_reg_field::type_id::create("ctrlupd_busy",,get_full_name());
      this.ctrlupd_busy.configure(this, 1, 17, "RO", 0, 1'h0, 1, 0, 0);
      this.ctrlupd_burst_busy = uvm_reg_field::type_id::create("ctrlupd_burst_busy",,get_full_name());
      this.ctrlupd_burst_busy.configure(this, 1, 18, "RO", 0, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLSTAT)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLSTAT
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLCAM1 extends uvm_reg;
	uvm_reg_field dbg_wrecc_q_depth;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dbg_wrecc_q_depth: coverpoint {m_data[6:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {8'b??????00};
	      wildcard bins bit_0_wr_as_1 = {8'b??????10};
	      wildcard bins bit_0_rd = {8'b???????1};
	      wildcard bins bit_1_wr_as_0 = {8'b?????0?0};
	      wildcard bins bit_1_wr_as_1 = {8'b?????1?0};
	      wildcard bins bit_1_rd = {8'b???????1};
	      wildcard bins bit_2_wr_as_0 = {8'b????0??0};
	      wildcard bins bit_2_wr_as_1 = {8'b????1??0};
	      wildcard bins bit_2_rd = {8'b???????1};
	      wildcard bins bit_3_wr_as_0 = {8'b???0???0};
	      wildcard bins bit_3_wr_as_1 = {8'b???1???0};
	      wildcard bins bit_3_rd = {8'b???????1};
	      wildcard bins bit_4_wr_as_0 = {8'b??0????0};
	      wildcard bins bit_4_wr_as_1 = {8'b??1????0};
	      wildcard bins bit_4_rd = {8'b???????1};
	      wildcard bins bit_5_wr_as_0 = {8'b?0?????0};
	      wildcard bins bit_5_wr_as_1 = {8'b?1?????0};
	      wildcard bins bit_5_rd = {8'b???????1};
	      wildcard bins bit_6_wr_as_0 = {8'b0??????0};
	      wildcard bins bit_6_wr_as_1 = {8'b1??????0};
	      wildcard bins bit_6_rd = {8'b???????1};
	      option.weight = 21;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLCAM1");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dbg_wrecc_q_depth = uvm_reg_field::type_id::create("dbg_wrecc_q_depth",,get_full_name());
      this.dbg_wrecc_q_depth.configure(this, 7, 0, "RO", 0, 7'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLCAM1)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLCAM1
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPREFCTRL0 extends uvm_reg;
	rand uvm_reg_field rank0_refresh;
	rand uvm_reg_field rank1_refresh;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   rank0_refresh: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   rank1_refresh: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_OPREFCTRL0");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.rank0_refresh = uvm_reg_field::type_id::create("rank0_refresh",,get_full_name());
      this.rank0_refresh.configure(this, 1, 0, "W1S", 0, 1'h0, 1, 0, 0);
      this.rank1_refresh = uvm_reg_field::type_id::create("rank1_refresh",,get_full_name());
      this.rank1_refresh.configure(this, 1, 1, "W1S", 0, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPREFCTRL0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPREFCTRL0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPREFSTAT0 extends uvm_reg;
	uvm_reg_field rank0_refresh_busy;
	uvm_reg_field rank1_refresh_busy;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   rank0_refresh_busy: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	   rank1_refresh_busy: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_OPREFSTAT0");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.rank0_refresh_busy = uvm_reg_field::type_id::create("rank0_refresh_busy",,get_full_name());
      this.rank0_refresh_busy.configure(this, 1, 0, "RO", 0, 1'h0, 1, 0, 0);
      this.rank1_refresh_busy = uvm_reg_field::type_id::create("rank1_refresh_busy",,get_full_name());
      this.rank1_refresh_busy.configure(this, 1, 1, "RO", 0, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPREFSTAT0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPREFSTAT0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SWCTL extends uvm_reg;
	rand uvm_reg_field sw_done;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   sw_done: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_SWCTL");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.sw_done = uvm_reg_field::type_id::create("sw_done",,get_full_name());
      this.sw_done.configure(this, 1, 0, "RW", 0, 1'h1, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SWCTL)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SWCTL
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SWSTAT extends uvm_reg;
	uvm_reg_field sw_done_ack;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   sw_done_ack: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_SWSTAT");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.sw_done_ack = uvm_reg_field::type_id::create("sw_done_ack",,get_full_name());
      this.sw_done_ack.configure(this, 1, 0, "RO", 0, 1'h1, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SWSTAT)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SWSTAT
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RANKCTL extends uvm_reg;
	rand uvm_reg_field max_rank_rd;
	rand uvm_reg_field max_rank_wr;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   max_rank_rd: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   max_rank_wr: coverpoint {m_data[15:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_RANKCTL");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.max_rank_rd = uvm_reg_field::type_id::create("max_rank_rd",,get_full_name());
      this.max_rank_rd.configure(this, 4, 0, "RW", 0, 4'hf, 1, 0, 1);
      this.max_rank_wr = uvm_reg_field::type_id::create("max_rank_wr",,get_full_name());
      this.max_rank_wr.configure(this, 4, 12, "RW", 0, 4'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RANKCTL)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RANKCTL
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DBICTL extends uvm_reg;
	rand uvm_reg_field dm_en;
	rand uvm_reg_field wr_dbi_en;
	rand uvm_reg_field rd_dbi_en;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   dm_en: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   wr_dbi_en: coverpoint {m_data[1:1], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   rd_dbi_en: coverpoint {m_data[2:2], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_DBICTL");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.dm_en = uvm_reg_field::type_id::create("dm_en",,get_full_name());
      this.dm_en.configure(this, 1, 0, "RW", 1, 1'h1, 1, 0, 0);
      this.wr_dbi_en = uvm_reg_field::type_id::create("wr_dbi_en",,get_full_name());
      this.wr_dbi_en.configure(this, 1, 1, "RW", 1, 1'h0, 1, 0, 0);
      this.rd_dbi_en = uvm_reg_field::type_id::create("rd_dbi_en",,get_full_name());
      this.rd_dbi_en.configure(this, 1, 2, "RW", 1, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DBICTL)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DBICTL
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ODTMAP extends uvm_reg;
	rand uvm_reg_field rank0_wr_odt;
	rand uvm_reg_field rank0_rd_odt;
	rand uvm_reg_field rank1_wr_odt;
	rand uvm_reg_field rank1_rd_odt;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   rank0_wr_odt: coverpoint {m_data[1:0], m_is_read} iff(m_be) {
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
	   rank0_rd_odt: coverpoint {m_data[5:4], m_is_read} iff(m_be) {
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
	   rank1_wr_odt: coverpoint {m_data[9:8], m_is_read} iff(m_be) {
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
	   rank1_rd_odt: coverpoint {m_data[13:12], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_ODTMAP");
		super.new(name, 16,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.rank0_wr_odt = uvm_reg_field::type_id::create("rank0_wr_odt",,get_full_name());
      this.rank0_wr_odt.configure(this, 2, 0, "RW", 0, 2'h1, 1, 0, 0);
      this.rank0_rd_odt = uvm_reg_field::type_id::create("rank0_rd_odt",,get_full_name());
      this.rank0_rd_odt.configure(this, 2, 4, "RW", 0, 2'h1, 1, 0, 0);
      this.rank1_wr_odt = uvm_reg_field::type_id::create("rank1_wr_odt",,get_full_name());
      this.rank1_wr_odt.configure(this, 2, 8, "RW", 0, 2'h2, 1, 0, 0);
      this.rank1_rd_odt = uvm_reg_field::type_id::create("rank1_rd_odt",,get_full_name());
      this.rank1_rd_odt.configure(this, 2, 12, "RW", 0, 2'h2, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ODTMAP)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ODTMAP
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DATACTL0 extends uvm_reg;
	rand uvm_reg_field rd_data_copy_en;
	rand uvm_reg_field wr_data_copy_en;
	rand uvm_reg_field wr_data_x_en;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   rd_data_copy_en: coverpoint {m_data[16:16], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   wr_data_copy_en: coverpoint {m_data[17:17], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   wr_data_x_en: coverpoint {m_data[18:18], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_DATACTL0");
		super.new(name, 24,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.rd_data_copy_en = uvm_reg_field::type_id::create("rd_data_copy_en",,get_full_name());
      this.rd_data_copy_en.configure(this, 1, 16, "RW", 1, 1'h0, 1, 0, 0);
      this.wr_data_copy_en = uvm_reg_field::type_id::create("wr_data_copy_en",,get_full_name());
      this.wr_data_copy_en.configure(this, 1, 17, "RW", 1, 1'h0, 1, 0, 0);
      this.wr_data_x_en = uvm_reg_field::type_id::create("wr_data_x_en",,get_full_name());
      this.wr_data_x_en.configure(this, 1, 18, "RW", 1, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DATACTL0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DATACTL0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SWCTLSTATIC extends uvm_reg;
	rand uvm_reg_field sw_static_unlock;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   sw_static_unlock: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_SWCTLSTATIC");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.sw_static_unlock = uvm_reg_field::type_id::create("sw_static_unlock",,get_full_name());
      this.sw_static_unlock.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SWCTLSTATIC)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SWCTLSTATIC
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_CGCTL extends uvm_reg;
	rand uvm_reg_field force_clk_te_en;
	rand uvm_reg_field force_clk_arb_en;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   force_clk_te_en: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   force_clk_arb_en: coverpoint {m_data[4:4], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_CGCTL");
		super.new(name, 8,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.force_clk_te_en = uvm_reg_field::type_id::create("force_clk_te_en",,get_full_name());
      this.force_clk_te_en.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 0);
      this.force_clk_arb_en = uvm_reg_field::type_id::create("force_clk_arb_en",,get_full_name());
      this.force_clk_arb_en.configure(this, 1, 4, "RW", 0, 1'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_CGCTL)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_CGCTL
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_INITTMG0 extends uvm_reg;
	rand uvm_reg_field pre_cke_x1024;
	rand uvm_reg_field post_cke_x1024;
	rand uvm_reg_field skip_dram_init;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   pre_cke_x1024: coverpoint {m_data[12:0], m_is_read} iff(m_be) {
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
	   post_cke_x1024: coverpoint {m_data[25:16], m_is_read} iff(m_be) {
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
	   skip_dram_init: coverpoint {m_data[31:30], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_INITTMG0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.pre_cke_x1024 = uvm_reg_field::type_id::create("pre_cke_x1024",,get_full_name());
      this.pre_cke_x1024.configure(this, 13, 0, "RW", 0, 13'h4e, 1, 0, 1);
      this.post_cke_x1024 = uvm_reg_field::type_id::create("post_cke_x1024",,get_full_name());
      this.post_cke_x1024.configure(this, 10, 16, "RW", 0, 10'h2, 1, 0, 0);
      this.skip_dram_init = uvm_reg_field::type_id::create("skip_dram_init",,get_full_name());
      this.skip_dram_init.configure(this, 2, 30, "RW", 1, 2'h0, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_INITTMG0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_INITTMG0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_PPT2CTRL0 extends uvm_reg;
	rand uvm_reg_field ppt2_burst_num;
	rand uvm_reg_field ppt2_ctrlupd_num_dfi0;
	rand uvm_reg_field ppt2_ctrlupd_num_dfi1;
	rand uvm_reg_field ppt2_burst;
	rand uvm_reg_field ppt2_wait_ref;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ppt2_burst_num: coverpoint {m_data[9:0], m_is_read} iff(m_be) {
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
	   ppt2_ctrlupd_num_dfi0: coverpoint {m_data[17:12], m_is_read} iff(m_be) {
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
	   ppt2_ctrlupd_num_dfi1: coverpoint {m_data[23:18], m_is_read} iff(m_be) {
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
	   ppt2_burst: coverpoint {m_data[28:28], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      //wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	   ppt2_wait_ref: coverpoint {m_data[31:31], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_PPT2CTRL0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ppt2_burst_num = uvm_reg_field::type_id::create("ppt2_burst_num",,get_full_name());
      this.ppt2_burst_num.configure(this, 10, 0, "RW", 0, 10'h200, 1, 0, 0);
      this.ppt2_ctrlupd_num_dfi0 = uvm_reg_field::type_id::create("ppt2_ctrlupd_num_dfi0",,get_full_name());
      this.ppt2_ctrlupd_num_dfi0.configure(this, 6, 12, "RW", 0, 6'h8, 1, 0, 0);
      this.ppt2_ctrlupd_num_dfi1 = uvm_reg_field::type_id::create("ppt2_ctrlupd_num_dfi1",,get_full_name());
      this.ppt2_ctrlupd_num_dfi1.configure(this, 6, 18, "RW", 0, 6'h0, 1, 0, 0);
      this.ppt2_burst = uvm_reg_field::type_id::create("ppt2_burst",,get_full_name());
      this.ppt2_burst.configure(this, 1, 28, "W1S", 0, 1'h0, 1, 0, 0);
      this.ppt2_wait_ref = uvm_reg_field::type_id::create("ppt2_wait_ref",,get_full_name());
      this.ppt2_wait_ref.configure(this, 1, 31, "RW", 0, 1'h1, 1, 0, 0);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_PPT2CTRL0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_PPT2CTRL0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_PPT2STAT0 extends uvm_reg;
	uvm_reg_field ppt2_state;
	uvm_reg_field ppt2_burst_busy;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ppt2_state: coverpoint {m_data[3:0], m_is_read} iff(m_be) {
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
	   ppt2_burst_busy: coverpoint {m_data[28:28], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd = {2'b?1};
	      option.weight = 3;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_PPT2STAT0");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ppt2_state = uvm_reg_field::type_id::create("ppt2_state",,get_full_name());
      this.ppt2_state.configure(this, 4, 0, "RO", 0, 4'h0, 1, 0, 1);
      this.ppt2_burst_busy = uvm_reg_field::type_id::create("ppt2_burst_busy",,get_full_name());
      this.ppt2_burst_busy.configure(this, 1, 28, "RO", 0, 1'h0, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_PPT2STAT0)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_PPT2STAT0
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DDRCTL_VER_NUMBER extends uvm_reg;
	uvm_reg_field ver_number;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ver_number: coverpoint {m_data[31:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {33'b???????????????????????????????00};
	      wildcard bins bit_0_wr_as_1 = {33'b???????????????????????????????10};
	      wildcard bins bit_0_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_1_wr_as_0 = {33'b??????????????????????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {33'b??????????????????????????????1?0};
	      wildcard bins bit_1_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_2_wr_as_0 = {33'b?????????????????????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {33'b?????????????????????????????1??0};
	      wildcard bins bit_2_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_3_wr_as_0 = {33'b????????????????????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {33'b????????????????????????????1???0};
	      wildcard bins bit_3_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_4_wr_as_0 = {33'b???????????????????????????0????0};
	      wildcard bins bit_4_wr_as_1 = {33'b???????????????????????????1????0};
	      wildcard bins bit_4_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_5_wr_as_0 = {33'b??????????????????????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {33'b??????????????????????????1?????0};
	      wildcard bins bit_5_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_6_wr_as_0 = {33'b?????????????????????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {33'b?????????????????????????1??????0};
	      wildcard bins bit_6_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_7_wr_as_0 = {33'b????????????????????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {33'b????????????????????????1???????0};
	      wildcard bins bit_7_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_8_wr_as_0 = {33'b???????????????????????0????????0};
	      wildcard bins bit_8_wr_as_1 = {33'b???????????????????????1????????0};
	      wildcard bins bit_8_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_9_wr_as_0 = {33'b??????????????????????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {33'b??????????????????????1?????????0};
	      wildcard bins bit_9_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_10_wr_as_0 = {33'b?????????????????????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {33'b?????????????????????1??????????0};
	      wildcard bins bit_10_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_11_wr_as_0 = {33'b????????????????????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {33'b????????????????????1???????????0};
	      wildcard bins bit_11_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_12_wr_as_0 = {33'b???????????????????0????????????0};
	      wildcard bins bit_12_wr_as_1 = {33'b???????????????????1????????????0};
	      wildcard bins bit_12_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_13_wr_as_0 = {33'b??????????????????0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {33'b??????????????????1?????????????0};
	      wildcard bins bit_13_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_14_wr_as_0 = {33'b?????????????????0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {33'b?????????????????1??????????????0};
	      wildcard bins bit_14_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_15_wr_as_0 = {33'b????????????????0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {33'b????????????????1???????????????0};
	      wildcard bins bit_15_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_16_wr_as_0 = {33'b???????????????0????????????????0};
	      wildcard bins bit_16_wr_as_1 = {33'b???????????????1????????????????0};
	      wildcard bins bit_16_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_17_wr_as_0 = {33'b??????????????0?????????????????0};
	      wildcard bins bit_17_wr_as_1 = {33'b??????????????1?????????????????0};
	      wildcard bins bit_17_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_18_wr_as_0 = {33'b?????????????0??????????????????0};
	      wildcard bins bit_18_wr_as_1 = {33'b?????????????1??????????????????0};
	      wildcard bins bit_18_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_19_wr_as_0 = {33'b????????????0???????????????????0};
	      wildcard bins bit_19_wr_as_1 = {33'b????????????1???????????????????0};
	      wildcard bins bit_19_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_20_wr_as_0 = {33'b???????????0????????????????????0};
	      wildcard bins bit_20_wr_as_1 = {33'b???????????1????????????????????0};
	      wildcard bins bit_20_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_21_wr_as_0 = {33'b??????????0?????????????????????0};
	      wildcard bins bit_21_wr_as_1 = {33'b??????????1?????????????????????0};
	      wildcard bins bit_21_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_22_wr_as_0 = {33'b?????????0??????????????????????0};
	      wildcard bins bit_22_wr_as_1 = {33'b?????????1??????????????????????0};
	      wildcard bins bit_22_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_23_wr_as_0 = {33'b????????0???????????????????????0};
	      wildcard bins bit_23_wr_as_1 = {33'b????????1???????????????????????0};
	      wildcard bins bit_23_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_24_wr_as_0 = {33'b???????0????????????????????????0};
	      wildcard bins bit_24_wr_as_1 = {33'b???????1????????????????????????0};
	      wildcard bins bit_24_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_25_wr_as_0 = {33'b??????0?????????????????????????0};
	      wildcard bins bit_25_wr_as_1 = {33'b??????1?????????????????????????0};
	      wildcard bins bit_25_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_26_wr_as_0 = {33'b?????0??????????????????????????0};
	      wildcard bins bit_26_wr_as_1 = {33'b?????1??????????????????????????0};
	      wildcard bins bit_26_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_27_wr_as_0 = {33'b????0???????????????????????????0};
	      wildcard bins bit_27_wr_as_1 = {33'b????1???????????????????????????0};
	      wildcard bins bit_27_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_28_wr_as_0 = {33'b???0????????????????????????????0};
	      wildcard bins bit_28_wr_as_1 = {33'b???1????????????????????????????0};
	      wildcard bins bit_28_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_29_wr_as_0 = {33'b??0?????????????????????????????0};
	      wildcard bins bit_29_wr_as_1 = {33'b??1?????????????????????????????0};
	      wildcard bins bit_29_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_30_wr_as_0 = {33'b?0??????????????????????????????0};
	      wildcard bins bit_30_wr_as_1 = {33'b?1??????????????????????????????0};
	      wildcard bins bit_30_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_31_wr_as_0 = {33'b0???????????????????????????????0};
	      wildcard bins bit_31_wr_as_1 = {33'b1???????????????????????????????0};
	      wildcard bins bit_31_rd = {33'b????????????????????????????????1};
	      option.weight = 96;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_DDRCTL_VER_NUMBER");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ver_number = uvm_reg_field::type_id::create("ver_number",,get_full_name());
      this.ver_number.configure(this, 32, 0, "RO", 0, 32'h3136302a, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DDRCTL_VER_NUMBER)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DDRCTL_VER_NUMBER
class ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DDRCTL_VER_TYPE extends uvm_reg;
	uvm_reg_field ver_type;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;
	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ver_type: coverpoint {m_data[31:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {33'b???????????????????????????????00};
	      wildcard bins bit_0_wr_as_1 = {33'b???????????????????????????????10};
	      wildcard bins bit_0_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_1_wr_as_0 = {33'b??????????????????????????????0?0};
	      wildcard bins bit_1_wr_as_1 = {33'b??????????????????????????????1?0};
	      wildcard bins bit_1_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_2_wr_as_0 = {33'b?????????????????????????????0??0};
	      wildcard bins bit_2_wr_as_1 = {33'b?????????????????????????????1??0};
	      wildcard bins bit_2_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_3_wr_as_0 = {33'b????????????????????????????0???0};
	      wildcard bins bit_3_wr_as_1 = {33'b????????????????????????????1???0};
	      wildcard bins bit_3_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_4_wr_as_0 = {33'b???????????????????????????0????0};
	      wildcard bins bit_4_wr_as_1 = {33'b???????????????????????????1????0};
	      wildcard bins bit_4_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_5_wr_as_0 = {33'b??????????????????????????0?????0};
	      wildcard bins bit_5_wr_as_1 = {33'b??????????????????????????1?????0};
	      wildcard bins bit_5_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_6_wr_as_0 = {33'b?????????????????????????0??????0};
	      wildcard bins bit_6_wr_as_1 = {33'b?????????????????????????1??????0};
	      wildcard bins bit_6_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_7_wr_as_0 = {33'b????????????????????????0???????0};
	      wildcard bins bit_7_wr_as_1 = {33'b????????????????????????1???????0};
	      wildcard bins bit_7_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_8_wr_as_0 = {33'b???????????????????????0????????0};
	      wildcard bins bit_8_wr_as_1 = {33'b???????????????????????1????????0};
	      wildcard bins bit_8_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_9_wr_as_0 = {33'b??????????????????????0?????????0};
	      wildcard bins bit_9_wr_as_1 = {33'b??????????????????????1?????????0};
	      wildcard bins bit_9_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_10_wr_as_0 = {33'b?????????????????????0??????????0};
	      wildcard bins bit_10_wr_as_1 = {33'b?????????????????????1??????????0};
	      wildcard bins bit_10_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_11_wr_as_0 = {33'b????????????????????0???????????0};
	      wildcard bins bit_11_wr_as_1 = {33'b????????????????????1???????????0};
	      wildcard bins bit_11_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_12_wr_as_0 = {33'b???????????????????0????????????0};
	      wildcard bins bit_12_wr_as_1 = {33'b???????????????????1????????????0};
	      wildcard bins bit_12_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_13_wr_as_0 = {33'b??????????????????0?????????????0};
	      wildcard bins bit_13_wr_as_1 = {33'b??????????????????1?????????????0};
	      wildcard bins bit_13_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_14_wr_as_0 = {33'b?????????????????0??????????????0};
	      wildcard bins bit_14_wr_as_1 = {33'b?????????????????1??????????????0};
	      wildcard bins bit_14_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_15_wr_as_0 = {33'b????????????????0???????????????0};
	      wildcard bins bit_15_wr_as_1 = {33'b????????????????1???????????????0};
	      wildcard bins bit_15_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_16_wr_as_0 = {33'b???????????????0????????????????0};
	      wildcard bins bit_16_wr_as_1 = {33'b???????????????1????????????????0};
	      wildcard bins bit_16_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_17_wr_as_0 = {33'b??????????????0?????????????????0};
	      wildcard bins bit_17_wr_as_1 = {33'b??????????????1?????????????????0};
	      wildcard bins bit_17_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_18_wr_as_0 = {33'b?????????????0??????????????????0};
	      wildcard bins bit_18_wr_as_1 = {33'b?????????????1??????????????????0};
	      wildcard bins bit_18_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_19_wr_as_0 = {33'b????????????0???????????????????0};
	      wildcard bins bit_19_wr_as_1 = {33'b????????????1???????????????????0};
	      wildcard bins bit_19_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_20_wr_as_0 = {33'b???????????0????????????????????0};
	      wildcard bins bit_20_wr_as_1 = {33'b???????????1????????????????????0};
	      wildcard bins bit_20_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_21_wr_as_0 = {33'b??????????0?????????????????????0};
	      wildcard bins bit_21_wr_as_1 = {33'b??????????1?????????????????????0};
	      wildcard bins bit_21_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_22_wr_as_0 = {33'b?????????0??????????????????????0};
	      wildcard bins bit_22_wr_as_1 = {33'b?????????1??????????????????????0};
	      wildcard bins bit_22_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_23_wr_as_0 = {33'b????????0???????????????????????0};
	      wildcard bins bit_23_wr_as_1 = {33'b????????1???????????????????????0};
	      wildcard bins bit_23_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_24_wr_as_0 = {33'b???????0????????????????????????0};
	      wildcard bins bit_24_wr_as_1 = {33'b???????1????????????????????????0};
	      wildcard bins bit_24_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_25_wr_as_0 = {33'b??????0?????????????????????????0};
	      wildcard bins bit_25_wr_as_1 = {33'b??????1?????????????????????????0};
	      wildcard bins bit_25_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_26_wr_as_0 = {33'b?????0??????????????????????????0};
	      wildcard bins bit_26_wr_as_1 = {33'b?????1??????????????????????????0};
	      wildcard bins bit_26_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_27_wr_as_0 = {33'b????0???????????????????????????0};
	      wildcard bins bit_27_wr_as_1 = {33'b????1???????????????????????????0};
	      wildcard bins bit_27_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_28_wr_as_0 = {33'b???0????????????????????????????0};
	      wildcard bins bit_28_wr_as_1 = {33'b???1????????????????????????????0};
	      wildcard bins bit_28_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_29_wr_as_0 = {33'b??0?????????????????????????????0};
	      wildcard bins bit_29_wr_as_1 = {33'b??1?????????????????????????????0};
	      wildcard bins bit_29_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_30_wr_as_0 = {33'b?0??????????????????????????????0};
	      wildcard bins bit_30_wr_as_1 = {33'b?1??????????????????????????????0};
	      wildcard bins bit_30_rd = {33'b????????????????????????????????1};
	      wildcard bins bit_31_wr_as_0 = {33'b0???????????????????????????????0};
	      wildcard bins bit_31_wr_as_1 = {33'b1???????????????????????????????0};
	      wildcard bins bit_31_rd = {33'b????????????????????????????????1};
	      option.weight = 96;
	   }
	endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0_DDRCTL_VER_TYPE");
		super.new(name, 32,build_coverage(UVM_CVR_REG_BITS));
		add_coverage(build_coverage(UVM_CVR_REG_BITS));
		if (has_coverage(UVM_CVR_REG_BITS))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ver_type = uvm_reg_field::type_id::create("ver_type",,get_full_name());
      this.ver_type.configure(this, 32, 0, "RO", 0, 32'h6c633030, 1, 0, 1);
   endfunction: build
	`uvm_object_utils(ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DDRCTL_VER_TYPE)
`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
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
endclass : ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DDRCTL_VER_TYPE
class ral_block_DWC_ddrctl_map_REGB_DDRC_CH0 extends uvm_reg_block;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MSTR0 MSTR0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MSTR2 MSTR2;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MSTR4 MSTR4;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_STAT STAT;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRCTRL0 MRCTRL0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRCTRL1 MRCTRL1;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRSTAT MRSTAT;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRRDATA0 MRRDATA0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRRDATA1 MRRDATA1;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL0 DERATECTL0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL1 DERATECTL1;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL2 DERATECTL2;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL5 DERATECTL5;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL6 DERATECTL6;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATESTAT0 DERATESTAT0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATEDBGCTL DERATEDBGCTL;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATEDBGSTAT DERATEDBGSTAT;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_PWRCTL PWRCTL;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_HWLPCTL HWLPCTL;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_CLKGATECTL CLKGATECTL;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFSHMOD0 RFSHMOD0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFSHCTL0 RFSHCTL0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFMMOD0 RFMMOD0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFMMOD1 RFMMOD1;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFMCTL RFMCTL;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFMSTAT RFMSTAT;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ZQCTL0 ZQCTL0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ZQCTL1 ZQCTL1;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ZQCTL2 ZQCTL2;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ZQSTAT ZQSTAT;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DQSOSCRUNTIME DQSOSCRUNTIME;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DQSOSCSTAT0 DQSOSCSTAT0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DQSOSCCFG0 DQSOSCCFG0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED0 SCHED0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED1 SCHED1;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED3 SCHED3;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED4 SCHED4;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED5 SCHED5;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_HWFFCCTL HWFFCCTL;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_HWFFCSTAT HWFFCSTAT;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFILPCFG0 DFILPCFG0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFIUPD0 DFIUPD0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFIMISC DFIMISC;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFISTAT DFISTAT;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFIPHYMSTR DFIPHYMSTR;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_POISONCFG POISONCFG;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_POISONSTAT POISONSTAT;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCFG0 ECCCFG0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCFG1 ECCCFG1;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCSTAT ECCSTAT;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCTL ECCCTL;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCERRCNT ECCERRCNT;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCADDR0 ECCCADDR0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCADDR1 ECCCADDR1;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCSYN0 ECCCSYN0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCSYN1 ECCCSYN1;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCSYN2 ECCCSYN2;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCBITMASK0 ECCBITMASK0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCBITMASK1 ECCBITMASK1;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCBITMASK2 ECCBITMASK2;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUADDR0 ECCUADDR0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUADDR1 ECCUADDR1;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUSYN0 ECCUSYN0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUSYN1 ECCUSYN1;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUSYN2 ECCUSYN2;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONADDR0 ECCPOISONADDR0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONADDR1 ECCPOISONADDR1;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONPAT0 ECCPOISONPAT0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONPAT2 ECCPOISONPAT2;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCAPSTAT ECCAPSTAT;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCCTL1 LNKECCCTL1;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCPOISONCTL0 LNKECCPOISONCTL0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCPOISONSTAT LNKECCPOISONSTAT;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCINDEX LNKECCINDEX;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCERRCNT0 LNKECCERRCNT0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCERRSTAT LNKECCERRSTAT;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCCADDR0 LNKECCCADDR0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCCADDR1 LNKECCCADDR1;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCUADDR0 LNKECCUADDR0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCUADDR1 LNKECCUADDR1;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRL0 OPCTRL0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRL1 OPCTRL1;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLCAM OPCTRLCAM;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLCMD OPCTRLCMD;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLSTAT OPCTRLSTAT;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLCAM1 OPCTRLCAM1;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPREFCTRL0 OPREFCTRL0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPREFSTAT0 OPREFSTAT0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SWCTL SWCTL;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SWSTAT SWSTAT;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RANKCTL RANKCTL;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DBICTL DBICTL;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ODTMAP ODTMAP;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DATACTL0 DATACTL0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SWCTLSTATIC SWCTLSTATIC;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_CGCTL CGCTL;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_INITTMG0 INITTMG0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_PPT2CTRL0 PPT2CTRL0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_PPT2STAT0 PPT2STAT0;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DDRCTL_VER_NUMBER DDRCTL_VER_NUMBER;
	rand ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DDRCTL_VER_TYPE DDRCTL_VER_TYPE;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field MSTR0_lpddr4;
	rand uvm_reg_field lpddr4;
	rand uvm_reg_field MSTR0_lpddr5;
	rand uvm_reg_field lpddr5;
	rand uvm_reg_field MSTR0_lpddr5x;
	rand uvm_reg_field lpddr5x;
	rand uvm_reg_field MSTR0_data_bus_width;
	rand uvm_reg_field data_bus_width;
	rand uvm_reg_field MSTR0_burst_rdwr;
	rand uvm_reg_field burst_rdwr;
	rand uvm_reg_field MSTR0_active_ranks;
	rand uvm_reg_field active_ranks;
	rand uvm_reg_field MSTR2_target_frequency;
	rand uvm_reg_field target_frequency;
	rand uvm_reg_field MSTR4_wck_on;
	rand uvm_reg_field wck_on;
	rand uvm_reg_field MSTR4_wck_suspend_en;
	rand uvm_reg_field wck_suspend_en;
	rand uvm_reg_field MSTR4_ws_off_en;
	rand uvm_reg_field ws_off_en;
	uvm_reg_field STAT_operating_mode;
	uvm_reg_field operating_mode;
	uvm_reg_field STAT_selfref_type;
	uvm_reg_field selfref_type;
	uvm_reg_field STAT_selfref_state;
	uvm_reg_field selfref_state;
	uvm_reg_field STAT_selfref_cam_not_empty;
	uvm_reg_field selfref_cam_not_empty;
	rand uvm_reg_field MRCTRL0_mr_type;
	rand uvm_reg_field mr_type;
	rand uvm_reg_field MRCTRL0_sw_init_int;
	rand uvm_reg_field sw_init_int;
	rand uvm_reg_field MRCTRL0_mr_rank;
	rand uvm_reg_field mr_rank;
	rand uvm_reg_field MRCTRL0_mr_addr;
	rand uvm_reg_field mr_addr;
	rand uvm_reg_field MRCTRL0_mrr_done_clr;
	rand uvm_reg_field mrr_done_clr;
	rand uvm_reg_field MRCTRL0_dis_mrrw_trfc;
	rand uvm_reg_field dis_mrrw_trfc;
	rand uvm_reg_field MRCTRL0_ppr_en;
	rand uvm_reg_field ppr_en;
	rand uvm_reg_field MRCTRL0_ppr_pgmpst_en;
	rand uvm_reg_field ppr_pgmpst_en;
	rand uvm_reg_field MRCTRL0_mr_wr;
	rand uvm_reg_field mr_wr;
	rand uvm_reg_field MRCTRL1_mr_data;
	rand uvm_reg_field mr_data;
	uvm_reg_field MRSTAT_mr_wr_busy;
	uvm_reg_field mr_wr_busy;
	uvm_reg_field MRSTAT_mrr_done;
	uvm_reg_field mrr_done;
	uvm_reg_field MRSTAT_ppr_done;
	uvm_reg_field ppr_done;
	uvm_reg_field MRRDATA0_mrr_data_lwr;
	uvm_reg_field mrr_data_lwr;
	uvm_reg_field MRRDATA1_mrr_data_upr;
	uvm_reg_field mrr_data_upr;
	rand uvm_reg_field DERATECTL0_derate_enable;
	rand uvm_reg_field derate_enable;
	rand uvm_reg_field DERATECTL0_lpddr4_refresh_mode;
	rand uvm_reg_field lpddr4_refresh_mode;
	rand uvm_reg_field DERATECTL0_derate_mr4_pause_fc;
	rand uvm_reg_field derate_mr4_pause_fc;
	rand uvm_reg_field DERATECTL0_dis_trefi_x6x8;
	rand uvm_reg_field dis_trefi_x6x8;
	rand uvm_reg_field DERATECTL0_dis_trefi_x0125;
	rand uvm_reg_field dis_trefi_x0125;
	rand uvm_reg_field DERATECTL0_use_slow_rm_in_low_temp;
	rand uvm_reg_field use_slow_rm_in_low_temp;
	rand uvm_reg_field DERATECTL1_active_derate_byte_rank0;
	rand uvm_reg_field active_derate_byte_rank0;
	rand uvm_reg_field DERATECTL2_active_derate_byte_rank1;
	rand uvm_reg_field active_derate_byte_rank1;
	rand uvm_reg_field DERATECTL5_derate_temp_limit_intr_en;
	rand uvm_reg_field derate_temp_limit_intr_en;
	rand uvm_reg_field DERATECTL5_derate_temp_limit_intr_clr;
	rand uvm_reg_field derate_temp_limit_intr_clr;
	rand uvm_reg_field DERATECTL5_derate_temp_limit_intr_force;
	rand uvm_reg_field derate_temp_limit_intr_force;
	rand uvm_reg_field DERATECTL6_derate_mr4_tuf_dis;
	rand uvm_reg_field derate_mr4_tuf_dis;
	uvm_reg_field DERATESTAT0_derate_temp_limit_intr;
	uvm_reg_field derate_temp_limit_intr;
	rand uvm_reg_field DERATEDBGCTL_dbg_mr4_rank_sel;
	rand uvm_reg_field dbg_mr4_rank_sel;
	uvm_reg_field DERATEDBGSTAT_dbg_mr4_byte0;
	uvm_reg_field dbg_mr4_byte0;
	uvm_reg_field DERATEDBGSTAT_dbg_mr4_byte1;
	uvm_reg_field dbg_mr4_byte1;
	uvm_reg_field DERATEDBGSTAT_dbg_mr4_byte2;
	uvm_reg_field dbg_mr4_byte2;
	uvm_reg_field DERATEDBGSTAT_dbg_mr4_byte3;
	uvm_reg_field dbg_mr4_byte3;
	rand uvm_reg_field PWRCTL_selfref_en;
	rand uvm_reg_field selfref_en;
	rand uvm_reg_field PWRCTL_powerdown_en;
	rand uvm_reg_field powerdown_en;
	rand uvm_reg_field PWRCTL_en_dfi_dram_clk_disable;
	rand uvm_reg_field en_dfi_dram_clk_disable;
	rand uvm_reg_field PWRCTL_selfref_sw;
	rand uvm_reg_field selfref_sw;
	rand uvm_reg_field PWRCTL_stay_in_selfref;
	rand uvm_reg_field stay_in_selfref;
	rand uvm_reg_field PWRCTL_dis_cam_drain_selfref;
	rand uvm_reg_field dis_cam_drain_selfref;
	rand uvm_reg_field PWRCTL_lpddr4_sr_allowed;
	rand uvm_reg_field lpddr4_sr_allowed;
	rand uvm_reg_field PWRCTL_dsm_en;
	rand uvm_reg_field dsm_en;
	rand uvm_reg_field HWLPCTL_hw_lp_en;
	rand uvm_reg_field hw_lp_en;
	rand uvm_reg_field HWLPCTL_hw_lp_exit_idle_en;
	rand uvm_reg_field hw_lp_exit_idle_en;
	rand uvm_reg_field CLKGATECTL_bsm_clk_on;
	rand uvm_reg_field bsm_clk_on;
	rand uvm_reg_field RFSHMOD0_refresh_burst;
	rand uvm_reg_field refresh_burst;
	rand uvm_reg_field RFSHMOD0_auto_refab_en;
	rand uvm_reg_field auto_refab_en;
	rand uvm_reg_field RFSHMOD0_per_bank_refresh;
	rand uvm_reg_field per_bank_refresh;
	rand uvm_reg_field RFSHMOD0_per_bank_refresh_opt_en;
	rand uvm_reg_field per_bank_refresh_opt_en;
	rand uvm_reg_field RFSHMOD0_fixed_crit_refpb_bank_en;
	rand uvm_reg_field fixed_crit_refpb_bank_en;
	rand uvm_reg_field RFSHCTL0_dis_auto_refresh;
	rand uvm_reg_field dis_auto_refresh;
	rand uvm_reg_field RFSHCTL0_refresh_update_level;
	rand uvm_reg_field refresh_update_level;
	rand uvm_reg_field RFMMOD0_rfm_en;
	rand uvm_reg_field rfm_en;
	rand uvm_reg_field RFMMOD0_rfmsbc;
	rand uvm_reg_field rfmsbc;
	rand uvm_reg_field RFMMOD0_raaimt;
	rand uvm_reg_field raaimt;
	rand uvm_reg_field RFMMOD0_raamult;
	rand uvm_reg_field raamult;
	rand uvm_reg_field RFMMOD0_raadec;
	rand uvm_reg_field raadec;
	rand uvm_reg_field RFMMOD0_rfmth_rm_thr;
	rand uvm_reg_field rfmth_rm_thr;
	rand uvm_reg_field RFMMOD1_init_raa_cnt;
	rand uvm_reg_field init_raa_cnt;
	rand uvm_reg_field RFMCTL_dbg_raa_rank;
	rand uvm_reg_field dbg_raa_rank;
	rand uvm_reg_field RFMCTL_dbg_raa_bg_bank;
	rand uvm_reg_field dbg_raa_bg_bank;
	uvm_reg_field RFMSTAT_rank_raa_cnt_gt0;
	uvm_reg_field rank_raa_cnt_gt0;
	uvm_reg_field RFMSTAT_dbg_raa_cnt;
	uvm_reg_field dbg_raa_cnt;
	rand uvm_reg_field ZQCTL0_zq_resistor_shared;
	rand uvm_reg_field zq_resistor_shared;
	rand uvm_reg_field ZQCTL0_dis_auto_zq;
	rand uvm_reg_field dis_auto_zq;
	rand uvm_reg_field ZQCTL1_zq_reset;
	rand uvm_reg_field zq_reset;
	rand uvm_reg_field ZQCTL2_dis_srx_zqcl;
	rand uvm_reg_field dis_srx_zqcl;
	rand uvm_reg_field ZQCTL2_dis_srx_zqcl_hwffc;
	rand uvm_reg_field dis_srx_zqcl_hwffc;
	uvm_reg_field ZQSTAT_zq_reset_busy;
	uvm_reg_field zq_reset_busy;
	rand uvm_reg_field DQSOSCRUNTIME_dqsosc_runtime;
	rand uvm_reg_field dqsosc_runtime;
	rand uvm_reg_field DQSOSCRUNTIME_wck2dqo_runtime;
	rand uvm_reg_field wck2dqo_runtime;
	uvm_reg_field DQSOSCSTAT0_dqsosc_state;
	uvm_reg_field dqsosc_state;
	uvm_reg_field DQSOSCSTAT0_dqsosc_per_rank_stat;
	uvm_reg_field dqsosc_per_rank_stat;
	rand uvm_reg_field DQSOSCCFG0_dis_dqsosc_srx;
	rand uvm_reg_field dis_dqsosc_srx;
	rand uvm_reg_field SCHED0_dis_opt_wrecc_collision_flush;
	rand uvm_reg_field dis_opt_wrecc_collision_flush;
	rand uvm_reg_field SCHED0_prefer_write;
	rand uvm_reg_field prefer_write;
	rand uvm_reg_field SCHED0_pageclose;
	rand uvm_reg_field pageclose;
	rand uvm_reg_field SCHED0_opt_wrcam_fill_level;
	rand uvm_reg_field opt_wrcam_fill_level;
	rand uvm_reg_field SCHED0_dis_opt_ntt_by_act;
	rand uvm_reg_field dis_opt_ntt_by_act;
	rand uvm_reg_field SCHED0_dis_opt_ntt_by_pre;
	rand uvm_reg_field dis_opt_ntt_by_pre;
	rand uvm_reg_field SCHED0_autopre_rmw;
	rand uvm_reg_field autopre_rmw;
	rand uvm_reg_field SCHED0_lpr_num_entries;
	rand uvm_reg_field lpr_num_entries;
	rand uvm_reg_field SCHED0_lpddr4_opt_act_timing;
	rand uvm_reg_field lpddr4_opt_act_timing;
	rand uvm_reg_field SCHED0_lpddr5_opt_act_timing;
	rand uvm_reg_field lpddr5_opt_act_timing;
	rand uvm_reg_field SCHED0_w_starve_free_running;
	rand uvm_reg_field w_starve_free_running;
	rand uvm_reg_field SCHED0_opt_act_lat;
	rand uvm_reg_field opt_act_lat;
	rand uvm_reg_field SCHED0_prefer_read;
	rand uvm_reg_field prefer_read;
	rand uvm_reg_field SCHED0_dis_speculative_act;
	rand uvm_reg_field dis_speculative_act;
	rand uvm_reg_field SCHED0_opt_vprw_sch;
	rand uvm_reg_field opt_vprw_sch;
	rand uvm_reg_field SCHED1_delay_switch_write;
	rand uvm_reg_field delay_switch_write;
	rand uvm_reg_field SCHED1_visible_window_limit_wr;
	rand uvm_reg_field visible_window_limit_wr;
	rand uvm_reg_field SCHED1_visible_window_limit_rd;
	rand uvm_reg_field visible_window_limit_rd;
	rand uvm_reg_field SCHED1_page_hit_limit_wr;
	rand uvm_reg_field page_hit_limit_wr;
	rand uvm_reg_field SCHED1_page_hit_limit_rd;
	rand uvm_reg_field page_hit_limit_rd;
	rand uvm_reg_field SCHED1_opt_hit_gt_hpr;
	rand uvm_reg_field opt_hit_gt_hpr;
	rand uvm_reg_field SCHED3_wrcam_lowthresh;
	rand uvm_reg_field wrcam_lowthresh;
	rand uvm_reg_field SCHED3_wrcam_highthresh;
	rand uvm_reg_field wrcam_highthresh;
	rand uvm_reg_field SCHED3_wr_pghit_num_thresh;
	rand uvm_reg_field wr_pghit_num_thresh;
	rand uvm_reg_field SCHED3_rd_pghit_num_thresh;
	rand uvm_reg_field rd_pghit_num_thresh;
	rand uvm_reg_field SCHED4_rd_act_idle_gap;
	rand uvm_reg_field rd_act_idle_gap;
	rand uvm_reg_field SCHED4_wr_act_idle_gap;
	rand uvm_reg_field wr_act_idle_gap;
	rand uvm_reg_field SCHED4_rd_page_exp_cycles;
	rand uvm_reg_field rd_page_exp_cycles;
	rand uvm_reg_field SCHED4_wr_page_exp_cycles;
	rand uvm_reg_field wr_page_exp_cycles;
	rand uvm_reg_field SCHED5_wrecc_cam_lowthresh;
	rand uvm_reg_field wrecc_cam_lowthresh;
	rand uvm_reg_field SCHED5_wrecc_cam_highthresh;
	rand uvm_reg_field wrecc_cam_highthresh;
	rand uvm_reg_field SCHED5_dis_opt_loaded_wrecc_cam_fill_level;
	rand uvm_reg_field dis_opt_loaded_wrecc_cam_fill_level;
	rand uvm_reg_field SCHED5_dis_opt_valid_wrecc_cam_fill_level;
	rand uvm_reg_field dis_opt_valid_wrecc_cam_fill_level;
	rand uvm_reg_field HWFFCCTL_hwffc_en;
	rand uvm_reg_field hwffc_en;
	rand uvm_reg_field HWFFCCTL_init_fsp;
	rand uvm_reg_field init_fsp;
	rand uvm_reg_field HWFFCCTL_init_vrcg;
	rand uvm_reg_field init_vrcg;
	rand uvm_reg_field HWFFCCTL_target_vrcg;
	rand uvm_reg_field target_vrcg;
	rand uvm_reg_field HWFFCCTL_skip_mrw_odtvref;
	rand uvm_reg_field skip_mrw_odtvref;
	rand uvm_reg_field HWFFCCTL_skip_zq_stop_start;
	rand uvm_reg_field skip_zq_stop_start;
	rand uvm_reg_field HWFFCCTL_zq_interval;
	rand uvm_reg_field zq_interval;
	rand uvm_reg_field HWFFCCTL_hwffc_mode;
	rand uvm_reg_field hwffc_mode;
	uvm_reg_field HWFFCSTAT_hwffc_in_progress;
	uvm_reg_field hwffc_in_progress;
	uvm_reg_field HWFFCSTAT_hwffc_operating_mode;
	uvm_reg_field hwffc_operating_mode;
	uvm_reg_field HWFFCSTAT_current_frequency;
	uvm_reg_field current_frequency;
	uvm_reg_field HWFFCSTAT_current_fsp;
	uvm_reg_field current_fsp;
	uvm_reg_field HWFFCSTAT_current_vrcg;
	uvm_reg_field current_vrcg;
	rand uvm_reg_field DFILPCFG0_dfi_lp_en_pd;
	rand uvm_reg_field dfi_lp_en_pd;
	rand uvm_reg_field DFILPCFG0_dfi_lp_en_sr;
	rand uvm_reg_field dfi_lp_en_sr;
	rand uvm_reg_field DFILPCFG0_dfi_lp_en_dsm;
	rand uvm_reg_field dfi_lp_en_dsm;
	rand uvm_reg_field DFILPCFG0_dfi_lp_en_data;
	rand uvm_reg_field dfi_lp_en_data;
	rand uvm_reg_field DFILPCFG0_dfi_lp_data_req_en;
	rand uvm_reg_field dfi_lp_data_req_en;
	rand uvm_reg_field DFILPCFG0_extra_gap_for_dfi_lp_data;
	rand uvm_reg_field extra_gap_for_dfi_lp_data;
	rand uvm_reg_field DFIUPD0_dfi_phyupd_en;
	rand uvm_reg_field dfi_phyupd_en;
	rand uvm_reg_field DFIUPD0_ctrlupd_pre_srx;
	rand uvm_reg_field ctrlupd_pre_srx;
	rand uvm_reg_field DFIUPD0_dis_auto_ctrlupd_srx;
	rand uvm_reg_field dis_auto_ctrlupd_srx;
	rand uvm_reg_field DFIUPD0_dis_auto_ctrlupd;
	rand uvm_reg_field dis_auto_ctrlupd;
	rand uvm_reg_field DFIMISC_dfi_init_complete_en;
	rand uvm_reg_field dfi_init_complete_en;
	rand uvm_reg_field DFIMISC_phy_dbi_mode;
	rand uvm_reg_field phy_dbi_mode;
	rand uvm_reg_field DFIMISC_dfi_data_cs_polarity;
	rand uvm_reg_field dfi_data_cs_polarity;
	rand uvm_reg_field DFIMISC_dfi_reset_n;
	rand uvm_reg_field dfi_reset_n;
	rand uvm_reg_field DFIMISC_dfi_init_start;
	rand uvm_reg_field dfi_init_start;
	rand uvm_reg_field DFIMISC_lp_optimized_write;
	rand uvm_reg_field lp_optimized_write;
	rand uvm_reg_field DFIMISC_dfi_frequency;
	rand uvm_reg_field dfi_frequency;
	rand uvm_reg_field DFIMISC_dfi_freq_fsp;
	rand uvm_reg_field dfi_freq_fsp;
	rand uvm_reg_field DFIMISC_dfi_channel_mode;
	rand uvm_reg_field dfi_channel_mode;
	uvm_reg_field DFISTAT_dfi_init_complete;
	uvm_reg_field dfi_init_complete;
	uvm_reg_field DFISTAT_dfi_lp_ctrl_ack_stat;
	uvm_reg_field dfi_lp_ctrl_ack_stat;
	uvm_reg_field DFISTAT_dfi_lp_data_ack_stat;
	uvm_reg_field dfi_lp_data_ack_stat;
	rand uvm_reg_field DFIPHYMSTR_dfi_phymstr_en;
	rand uvm_reg_field dfi_phymstr_en;
	rand uvm_reg_field DFIPHYMSTR_dfi_phymstr_blk_ref_x32;
	rand uvm_reg_field dfi_phymstr_blk_ref_x32;
	rand uvm_reg_field POISONCFG_wr_poison_slverr_en;
	rand uvm_reg_field wr_poison_slverr_en;
	rand uvm_reg_field POISONCFG_wr_poison_intr_en;
	rand uvm_reg_field wr_poison_intr_en;
	rand uvm_reg_field POISONCFG_wr_poison_intr_clr;
	rand uvm_reg_field wr_poison_intr_clr;
	rand uvm_reg_field POISONCFG_rd_poison_slverr_en;
	rand uvm_reg_field rd_poison_slverr_en;
	rand uvm_reg_field POISONCFG_rd_poison_intr_en;
	rand uvm_reg_field rd_poison_intr_en;
	rand uvm_reg_field POISONCFG_rd_poison_intr_clr;
	rand uvm_reg_field rd_poison_intr_clr;
	uvm_reg_field POISONSTAT_wr_poison_intr_0;
	uvm_reg_field wr_poison_intr_0;
	uvm_reg_field POISONSTAT_rd_poison_intr_0;
	uvm_reg_field rd_poison_intr_0;
	rand uvm_reg_field ECCCFG0_ecc_mode;
	rand uvm_reg_field ecc_mode;
	rand uvm_reg_field ECCCFG0_ecc_ap_en;
	rand uvm_reg_field ecc_ap_en;
	rand uvm_reg_field ECCCFG0_ecc_region_remap_en;
	rand uvm_reg_field ecc_region_remap_en;
	rand uvm_reg_field ECCCFG0_ecc_region_map;
	rand uvm_reg_field ecc_region_map;
	rand uvm_reg_field ECCCFG0_blk_channel_idle_time_x32;
	rand uvm_reg_field blk_channel_idle_time_x32;
	rand uvm_reg_field ECCCFG0_ecc_ap_err_threshold;
	rand uvm_reg_field ecc_ap_err_threshold;
	rand uvm_reg_field ECCCFG0_ecc_region_map_other;
	rand uvm_reg_field ecc_region_map_other;
	rand uvm_reg_field ECCCFG0_ecc_region_map_granu;
	rand uvm_reg_field ecc_region_map_granu;
	rand uvm_reg_field ECCCFG1_data_poison_en;
	rand uvm_reg_field data_poison_en;
	rand uvm_reg_field ECCCFG1_data_poison_bit;
	rand uvm_reg_field data_poison_bit;
	rand uvm_reg_field ECCCFG1_ecc_region_parity_lock;
	rand uvm_reg_field ecc_region_parity_lock;
	rand uvm_reg_field ECCCFG1_ecc_region_waste_lock;
	rand uvm_reg_field ecc_region_waste_lock;
	rand uvm_reg_field ECCCFG1_med_ecc_en;
	rand uvm_reg_field med_ecc_en;
	rand uvm_reg_field ECCCFG1_blk_channel_active_term;
	rand uvm_reg_field blk_channel_active_term;
	rand uvm_reg_field ECCCFG1_active_blk_channel;
	rand uvm_reg_field active_blk_channel;
	uvm_reg_field ECCSTAT_ecc_corrected_bit_num;
	uvm_reg_field ecc_corrected_bit_num;
	uvm_reg_field ECCSTAT_ecc_corrected_err;
	uvm_reg_field ecc_corrected_err;
	uvm_reg_field ECCSTAT_ecc_uncorrected_err;
	uvm_reg_field ecc_uncorrected_err;
	uvm_reg_field ECCSTAT_sbr_read_ecc_ce;
	uvm_reg_field sbr_read_ecc_ce;
	uvm_reg_field ECCSTAT_sbr_read_ecc_ue;
	uvm_reg_field sbr_read_ecc_ue;
	rand uvm_reg_field ECCCTL_ecc_corrected_err_clr;
	rand uvm_reg_field ecc_corrected_err_clr;
	rand uvm_reg_field ECCCTL_ecc_uncorrected_err_clr;
	rand uvm_reg_field ecc_uncorrected_err_clr;
	rand uvm_reg_field ECCCTL_ecc_corr_err_cnt_clr;
	rand uvm_reg_field ecc_corr_err_cnt_clr;
	rand uvm_reg_field ECCCTL_ecc_uncorr_err_cnt_clr;
	rand uvm_reg_field ecc_uncorr_err_cnt_clr;
	rand uvm_reg_field ECCCTL_ecc_ap_err_intr_clr;
	rand uvm_reg_field ecc_ap_err_intr_clr;
	rand uvm_reg_field ECCCTL_ecc_corrected_err_intr_en;
	rand uvm_reg_field ecc_corrected_err_intr_en;
	rand uvm_reg_field ECCCTL_ecc_uncorrected_err_intr_en;
	rand uvm_reg_field ecc_uncorrected_err_intr_en;
	rand uvm_reg_field ECCCTL_ecc_ap_err_intr_en;
	rand uvm_reg_field ecc_ap_err_intr_en;
	rand uvm_reg_field ECCCTL_ecc_corrected_err_intr_force;
	rand uvm_reg_field ecc_corrected_err_intr_force;
	rand uvm_reg_field ECCCTL_ecc_uncorrected_err_intr_force;
	rand uvm_reg_field ecc_uncorrected_err_intr_force;
	rand uvm_reg_field ECCCTL_ecc_ap_err_intr_force;
	rand uvm_reg_field ecc_ap_err_intr_force;
	uvm_reg_field ECCERRCNT_ecc_corr_err_cnt;
	uvm_reg_field ecc_corr_err_cnt;
	uvm_reg_field ECCERRCNT_ecc_uncorr_err_cnt;
	uvm_reg_field ecc_uncorr_err_cnt;
	uvm_reg_field ECCCADDR0_ecc_corr_row;
	uvm_reg_field ecc_corr_row;
	uvm_reg_field ECCCADDR0_ecc_corr_rank;
	uvm_reg_field ecc_corr_rank;
	uvm_reg_field ECCCADDR1_ecc_corr_col;
	uvm_reg_field ecc_corr_col;
	uvm_reg_field ECCCADDR1_ecc_corr_bank;
	uvm_reg_field ecc_corr_bank;
	uvm_reg_field ECCCADDR1_ecc_corr_bg;
	uvm_reg_field ecc_corr_bg;
	uvm_reg_field ECCCSYN0_ecc_corr_syndromes_31_0;
	uvm_reg_field ecc_corr_syndromes_31_0;
	uvm_reg_field ECCCSYN1_ecc_corr_syndromes_63_32;
	uvm_reg_field ecc_corr_syndromes_63_32;
	uvm_reg_field ECCCSYN2_ecc_corr_syndromes_71_64;
	uvm_reg_field ecc_corr_syndromes_71_64;
	uvm_reg_field ECCBITMASK0_ecc_corr_bit_mask_31_0;
	uvm_reg_field ecc_corr_bit_mask_31_0;
	uvm_reg_field ECCBITMASK1_ecc_corr_bit_mask_63_32;
	uvm_reg_field ecc_corr_bit_mask_63_32;
	uvm_reg_field ECCBITMASK2_ecc_corr_bit_mask_71_64;
	uvm_reg_field ecc_corr_bit_mask_71_64;
	uvm_reg_field ECCUADDR0_ecc_uncorr_row;
	uvm_reg_field ecc_uncorr_row;
	uvm_reg_field ECCUADDR0_ecc_uncorr_rank;
	uvm_reg_field ecc_uncorr_rank;
	uvm_reg_field ECCUADDR1_ecc_uncorr_col;
	uvm_reg_field ecc_uncorr_col;
	uvm_reg_field ECCUADDR1_ecc_uncorr_bank;
	uvm_reg_field ecc_uncorr_bank;
	uvm_reg_field ECCUADDR1_ecc_uncorr_bg;
	uvm_reg_field ecc_uncorr_bg;
	uvm_reg_field ECCUSYN0_ecc_uncorr_syndromes_31_0;
	uvm_reg_field ecc_uncorr_syndromes_31_0;
	uvm_reg_field ECCUSYN1_ecc_uncorr_syndromes_63_32;
	uvm_reg_field ecc_uncorr_syndromes_63_32;
	uvm_reg_field ECCUSYN2_ecc_uncorr_syndromes_71_64;
	uvm_reg_field ecc_uncorr_syndromes_71_64;
	rand uvm_reg_field ECCPOISONADDR0_ecc_poison_col;
	rand uvm_reg_field ecc_poison_col;
	rand uvm_reg_field ECCPOISONADDR0_ecc_poison_rank;
	rand uvm_reg_field ecc_poison_rank;
	rand uvm_reg_field ECCPOISONADDR1_ecc_poison_row;
	rand uvm_reg_field ecc_poison_row;
	rand uvm_reg_field ECCPOISONADDR1_ecc_poison_bank;
	rand uvm_reg_field ecc_poison_bank;
	rand uvm_reg_field ECCPOISONADDR1_ecc_poison_bg;
	rand uvm_reg_field ecc_poison_bg;
	rand uvm_reg_field ECCPOISONPAT0_ecc_poison_data_31_0;
	rand uvm_reg_field ecc_poison_data_31_0;
	rand uvm_reg_field ECCPOISONPAT2_ecc_poison_data_71_64;
	rand uvm_reg_field ecc_poison_data_71_64;
	uvm_reg_field ECCAPSTAT_ecc_ap_err;
	uvm_reg_field ecc_ap_err;
	rand uvm_reg_field LNKECCCTL1_rd_link_ecc_corr_intr_en;
	rand uvm_reg_field rd_link_ecc_corr_intr_en;
	rand uvm_reg_field LNKECCCTL1_rd_link_ecc_corr_intr_clr;
	rand uvm_reg_field rd_link_ecc_corr_intr_clr;
	rand uvm_reg_field LNKECCCTL1_rd_link_ecc_corr_cnt_clr;
	rand uvm_reg_field rd_link_ecc_corr_cnt_clr;
	rand uvm_reg_field LNKECCCTL1_rd_link_ecc_corr_intr_force;
	rand uvm_reg_field rd_link_ecc_corr_intr_force;
	rand uvm_reg_field LNKECCCTL1_rd_link_ecc_uncorr_intr_en;
	rand uvm_reg_field rd_link_ecc_uncorr_intr_en;
	rand uvm_reg_field LNKECCCTL1_rd_link_ecc_uncorr_intr_clr;
	rand uvm_reg_field rd_link_ecc_uncorr_intr_clr;
	rand uvm_reg_field LNKECCCTL1_rd_link_ecc_uncorr_cnt_clr;
	rand uvm_reg_field rd_link_ecc_uncorr_cnt_clr;
	rand uvm_reg_field LNKECCCTL1_rd_link_ecc_uncorr_intr_force;
	rand uvm_reg_field rd_link_ecc_uncorr_intr_force;
	rand uvm_reg_field LNKECCPOISONCTL0_linkecc_poison_inject_en;
	rand uvm_reg_field linkecc_poison_inject_en;
	rand uvm_reg_field LNKECCPOISONCTL0_linkecc_poison_type;
	rand uvm_reg_field linkecc_poison_type;
	rand uvm_reg_field LNKECCPOISONCTL0_linkecc_poison_rw;
	rand uvm_reg_field linkecc_poison_rw;
	rand uvm_reg_field LNKECCPOISONCTL0_linkecc_poison_dmi_sel;
	rand uvm_reg_field linkecc_poison_dmi_sel;
	rand uvm_reg_field LNKECCPOISONCTL0_linkecc_poison_byte_sel;
	rand uvm_reg_field linkecc_poison_byte_sel;
	uvm_reg_field LNKECCPOISONSTAT_linkecc_poison_complete;
	uvm_reg_field linkecc_poison_complete;
	rand uvm_reg_field LNKECCINDEX_rd_link_ecc_err_byte_sel;
	rand uvm_reg_field rd_link_ecc_err_byte_sel;
	rand uvm_reg_field LNKECCINDEX_rd_link_ecc_err_rank_sel;
	rand uvm_reg_field rd_link_ecc_err_rank_sel;
	uvm_reg_field LNKECCERRCNT0_rd_link_ecc_err_syndrome;
	uvm_reg_field rd_link_ecc_err_syndrome;
	uvm_reg_field LNKECCERRCNT0_rd_link_ecc_corr_cnt;
	uvm_reg_field rd_link_ecc_corr_cnt;
	uvm_reg_field LNKECCERRCNT0_rd_link_ecc_uncorr_cnt;
	uvm_reg_field rd_link_ecc_uncorr_cnt;
	uvm_reg_field LNKECCERRSTAT_rd_link_ecc_corr_err_int;
	uvm_reg_field rd_link_ecc_corr_err_int;
	uvm_reg_field LNKECCERRSTAT_rd_link_ecc_uncorr_err_int;
	uvm_reg_field rd_link_ecc_uncorr_err_int;
	uvm_reg_field LNKECCCADDR0_link_ecc_corr_row;
	uvm_reg_field link_ecc_corr_row;
	uvm_reg_field LNKECCCADDR0_link_ecc_corr_rank;
	uvm_reg_field link_ecc_corr_rank;
	uvm_reg_field LNKECCCADDR1_link_ecc_corr_col;
	uvm_reg_field link_ecc_corr_col;
	uvm_reg_field LNKECCCADDR1_link_ecc_corr_bank;
	uvm_reg_field link_ecc_corr_bank;
	uvm_reg_field LNKECCCADDR1_link_ecc_corr_bg;
	uvm_reg_field link_ecc_corr_bg;
	uvm_reg_field LNKECCUADDR0_link_ecc_uncorr_row;
	uvm_reg_field link_ecc_uncorr_row;
	uvm_reg_field LNKECCUADDR0_link_ecc_uncorr_rank;
	uvm_reg_field link_ecc_uncorr_rank;
	uvm_reg_field LNKECCUADDR1_link_ecc_uncorr_col;
	uvm_reg_field link_ecc_uncorr_col;
	uvm_reg_field LNKECCUADDR1_link_ecc_uncorr_bank;
	uvm_reg_field link_ecc_uncorr_bank;
	uvm_reg_field LNKECCUADDR1_link_ecc_uncorr_bg;
	uvm_reg_field link_ecc_uncorr_bg;
	rand uvm_reg_field OPCTRL0_dis_wc;
	rand uvm_reg_field dis_wc;
	rand uvm_reg_field OPCTRL0_dis_max_rank_rd_opt;
	rand uvm_reg_field dis_max_rank_rd_opt;
	rand uvm_reg_field OPCTRL0_dis_max_rank_wr_opt;
	rand uvm_reg_field dis_max_rank_wr_opt;
	rand uvm_reg_field OPCTRL1_dis_dq;
	rand uvm_reg_field dis_dq;
	rand uvm_reg_field OPCTRL1_dis_hif;
	rand uvm_reg_field dis_hif;
	uvm_reg_field OPCTRLCAM_dbg_hpr_q_depth;
	uvm_reg_field dbg_hpr_q_depth;
	uvm_reg_field OPCTRLCAM_dbg_lpr_q_depth;
	uvm_reg_field dbg_lpr_q_depth;
	uvm_reg_field OPCTRLCAM_dbg_w_q_depth;
	uvm_reg_field dbg_w_q_depth;
	uvm_reg_field OPCTRLCAM_dbg_stall;
	uvm_reg_field dbg_stall;
	uvm_reg_field OPCTRLCAM_dbg_rd_q_empty;
	uvm_reg_field dbg_rd_q_empty;
	uvm_reg_field OPCTRLCAM_dbg_wr_q_empty;
	uvm_reg_field dbg_wr_q_empty;
	uvm_reg_field OPCTRLCAM_rd_data_pipeline_empty;
	uvm_reg_field rd_data_pipeline_empty;
	uvm_reg_field OPCTRLCAM_wr_data_pipeline_empty;
	uvm_reg_field wr_data_pipeline_empty;
	rand uvm_reg_field OPCTRLCMD_zq_calib_short;
	rand uvm_reg_field zq_calib_short;
	rand uvm_reg_field OPCTRLCMD_ctrlupd;
	rand uvm_reg_field ctrlupd;
	rand uvm_reg_field OPCTRLCMD_ctrlupd_burst;
	rand uvm_reg_field ctrlupd_burst;
	uvm_reg_field OPCTRLSTAT_zq_calib_short_busy;
	uvm_reg_field zq_calib_short_busy;
	uvm_reg_field OPCTRLSTAT_ctrlupd_busy;
	uvm_reg_field ctrlupd_busy;
	uvm_reg_field OPCTRLSTAT_ctrlupd_burst_busy;
	uvm_reg_field ctrlupd_burst_busy;
	uvm_reg_field OPCTRLCAM1_dbg_wrecc_q_depth;
	uvm_reg_field dbg_wrecc_q_depth;
	rand uvm_reg_field OPREFCTRL0_rank0_refresh;
	rand uvm_reg_field rank0_refresh;
	rand uvm_reg_field OPREFCTRL0_rank1_refresh;
	rand uvm_reg_field rank1_refresh;
	uvm_reg_field OPREFSTAT0_rank0_refresh_busy;
	uvm_reg_field rank0_refresh_busy;
	uvm_reg_field OPREFSTAT0_rank1_refresh_busy;
	uvm_reg_field rank1_refresh_busy;
	rand uvm_reg_field SWCTL_sw_done;
	rand uvm_reg_field sw_done;
	uvm_reg_field SWSTAT_sw_done_ack;
	uvm_reg_field sw_done_ack;
	rand uvm_reg_field RANKCTL_max_rank_rd;
	rand uvm_reg_field max_rank_rd;
	rand uvm_reg_field RANKCTL_max_rank_wr;
	rand uvm_reg_field max_rank_wr;
	rand uvm_reg_field DBICTL_dm_en;
	rand uvm_reg_field dm_en;
	rand uvm_reg_field DBICTL_wr_dbi_en;
	rand uvm_reg_field wr_dbi_en;
	rand uvm_reg_field DBICTL_rd_dbi_en;
	rand uvm_reg_field rd_dbi_en;
	rand uvm_reg_field ODTMAP_rank0_wr_odt;
	rand uvm_reg_field rank0_wr_odt;
	rand uvm_reg_field ODTMAP_rank0_rd_odt;
	rand uvm_reg_field rank0_rd_odt;
	rand uvm_reg_field ODTMAP_rank1_wr_odt;
	rand uvm_reg_field rank1_wr_odt;
	rand uvm_reg_field ODTMAP_rank1_rd_odt;
	rand uvm_reg_field rank1_rd_odt;
	rand uvm_reg_field DATACTL0_rd_data_copy_en;
	rand uvm_reg_field rd_data_copy_en;
	rand uvm_reg_field DATACTL0_wr_data_copy_en;
	rand uvm_reg_field wr_data_copy_en;
	rand uvm_reg_field DATACTL0_wr_data_x_en;
	rand uvm_reg_field wr_data_x_en;
	rand uvm_reg_field SWCTLSTATIC_sw_static_unlock;
	rand uvm_reg_field sw_static_unlock;
	rand uvm_reg_field CGCTL_force_clk_te_en;
	rand uvm_reg_field force_clk_te_en;
	rand uvm_reg_field CGCTL_force_clk_arb_en;
	rand uvm_reg_field force_clk_arb_en;
	rand uvm_reg_field INITTMG0_pre_cke_x1024;
	rand uvm_reg_field pre_cke_x1024;
	rand uvm_reg_field INITTMG0_post_cke_x1024;
	rand uvm_reg_field post_cke_x1024;
	rand uvm_reg_field INITTMG0_skip_dram_init;
	rand uvm_reg_field skip_dram_init;
	rand uvm_reg_field PPT2CTRL0_ppt2_burst_num;
	rand uvm_reg_field ppt2_burst_num;
	rand uvm_reg_field PPT2CTRL0_ppt2_ctrlupd_num_dfi0;
	rand uvm_reg_field ppt2_ctrlupd_num_dfi0;
	rand uvm_reg_field PPT2CTRL0_ppt2_ctrlupd_num_dfi1;
	rand uvm_reg_field ppt2_ctrlupd_num_dfi1;
	rand uvm_reg_field PPT2CTRL0_ppt2_burst;
	rand uvm_reg_field ppt2_burst;
	rand uvm_reg_field PPT2CTRL0_ppt2_wait_ref;
	rand uvm_reg_field ppt2_wait_ref;
	uvm_reg_field PPT2STAT0_ppt2_state;
	uvm_reg_field ppt2_state;
	uvm_reg_field PPT2STAT0_ppt2_burst_busy;
	uvm_reg_field ppt2_burst_busy;
	uvm_reg_field DDRCTL_VER_NUMBER_ver_number;
	uvm_reg_field ver_number;
	uvm_reg_field DDRCTL_VER_TYPE_ver_type;
	uvm_reg_field ver_type;
	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();
	MSTR0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h0 };
		option.weight = 1;
	}
	MSTR2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h8 };
		option.weight = 1;
	}
	MSTR4 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h10 };
		option.weight = 1;
	}
	STAT : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h14 };
		option.weight = 1;
	}
	MRCTRL0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h80 };
		option.weight = 1;
	}
	MRCTRL1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h84 };
		option.weight = 1;
	}
	MRSTAT : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h90 };
		option.weight = 1;
	}
	MRRDATA0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h94 };
		option.weight = 1;
	}
	MRRDATA1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h98 };
		option.weight = 1;
	}
	DERATECTL0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h100 };
		option.weight = 1;
	}
	DERATECTL1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h104 };
		option.weight = 1;
	}
	DERATECTL2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h108 };
		option.weight = 1;
	}
	DERATECTL5 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h114 };
		option.weight = 1;
	}
	DERATECTL6 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h118 };
		option.weight = 1;
	}
	DERATESTAT0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h120 };
		option.weight = 1;
	}
	DERATEDBGCTL : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h128 };
		option.weight = 1;
	}
	DERATEDBGSTAT : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h12C };
		option.weight = 1;
	}
	PWRCTL : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h180 };
		option.weight = 1;
	}
	HWLPCTL : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h184 };
		option.weight = 1;
	}
	CLKGATECTL : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h18C };
		option.weight = 1;
	}
	RFSHMOD0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h200 };
		option.weight = 1;
	}
	RFSHCTL0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h208 };
		option.weight = 1;
	}
	RFMMOD0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h220 };
		option.weight = 1;
	}
	RFMMOD1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h224 };
		option.weight = 1;
	}
	RFMCTL : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h228 };
		option.weight = 1;
	}
	RFMSTAT : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h22C };
		option.weight = 1;
	}
	ZQCTL0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h280 };
		option.weight = 1;
	}
	ZQCTL1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h284 };
		option.weight = 1;
	}
	ZQCTL2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h288 };
		option.weight = 1;
	}
	ZQSTAT : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h28C };
		option.weight = 1;
	}
	DQSOSCRUNTIME : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h300 };
		option.weight = 1;
	}
	DQSOSCSTAT0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h304 };
		option.weight = 1;
	}
	DQSOSCCFG0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h308 };
		option.weight = 1;
	}
	SCHED0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h380 };
		option.weight = 1;
	}
	SCHED1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h384 };
		option.weight = 1;
	}
	SCHED3 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h38C };
		option.weight = 1;
	}
	SCHED4 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h390 };
		option.weight = 1;
	}
	SCHED5 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h394 };
		option.weight = 1;
	}
	HWFFCCTL : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h400 };
		option.weight = 1;
	}
	HWFFCSTAT : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h404 };
		option.weight = 1;
	}
	DFILPCFG0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h500 };
		option.weight = 1;
	}
	DFIUPD0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h508 };
		option.weight = 1;
	}
	DFIMISC : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h510 };
		option.weight = 1;
	}
	DFISTAT : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h514 };
		option.weight = 1;
	}
	DFIPHYMSTR : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h518 };
		option.weight = 1;
	}
	POISONCFG : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h580 };
		option.weight = 1;
	}
	POISONSTAT : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h584 };
		option.weight = 1;
	}
	ECCCFG0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h600 };
		option.weight = 1;
	}
	ECCCFG1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h604 };
		option.weight = 1;
	}
	ECCSTAT : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h608 };
		option.weight = 1;
	}
	ECCCTL : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h60C };
		option.weight = 1;
	}
	ECCERRCNT : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h610 };
		option.weight = 1;
	}
	ECCCADDR0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h614 };
		option.weight = 1;
	}
	ECCCADDR1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h618 };
		option.weight = 1;
	}
	ECCCSYN0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h61C };
		option.weight = 1;
	}
	ECCCSYN1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h620 };
		option.weight = 1;
	}
	ECCCSYN2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h624 };
		option.weight = 1;
	}
	ECCBITMASK0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h628 };
		option.weight = 1;
	}
	ECCBITMASK1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h62C };
		option.weight = 1;
	}
	ECCBITMASK2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h630 };
		option.weight = 1;
	}
	ECCUADDR0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h634 };
		option.weight = 1;
	}
	ECCUADDR1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h638 };
		option.weight = 1;
	}
	ECCUSYN0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h63C };
		option.weight = 1;
	}
	ECCUSYN1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h640 };
		option.weight = 1;
	}
	ECCUSYN2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h644 };
		option.weight = 1;
	}
	ECCPOISONADDR0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h648 };
		option.weight = 1;
	}
	ECCPOISONADDR1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h64C };
		option.weight = 1;
	}
	ECCPOISONPAT0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h658 };
		option.weight = 1;
	}
	ECCPOISONPAT2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h660 };
		option.weight = 1;
	}
	ECCAPSTAT : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h664 };
		option.weight = 1;
	}
	LNKECCCTL1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h984 };
		option.weight = 1;
	}
	LNKECCPOISONCTL0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h988 };
		option.weight = 1;
	}
	LNKECCPOISONSTAT : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h98C };
		option.weight = 1;
	}
	LNKECCINDEX : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h990 };
		option.weight = 1;
	}
	LNKECCERRCNT0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h994 };
		option.weight = 1;
	}
	LNKECCERRSTAT : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h998 };
		option.weight = 1;
	}
	LNKECCCADDR0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h9E0 };
		option.weight = 1;
	}
	LNKECCCADDR1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h9E4 };
		option.weight = 1;
	}
	LNKECCUADDR0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h9E8 };
		option.weight = 1;
	}
	LNKECCUADDR1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h9EC };
		option.weight = 1;
	}
	OPCTRL0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB80 };
		option.weight = 1;
	}
	OPCTRL1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB84 };
		option.weight = 1;
	}
	OPCTRLCAM : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB88 };
		option.weight = 1;
	}
	OPCTRLCMD : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB8C };
		option.weight = 1;
	}
	OPCTRLSTAT : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB90 };
		option.weight = 1;
	}
	OPCTRLCAM1 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB94 };
		option.weight = 1;
	}
	OPREFCTRL0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hB98 };
		option.weight = 1;
	}
	OPREFSTAT0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hBA0 };
		option.weight = 1;
	}
	SWCTL : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC80 };
		option.weight = 1;
	}
	SWSTAT : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC84 };
		option.weight = 1;
	}
	RANKCTL : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC90 };
		option.weight = 1;
	}
	DBICTL : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC94 };
		option.weight = 1;
	}
	ODTMAP : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hC9C };
		option.weight = 1;
	}
	DATACTL0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hCA0 };
		option.weight = 1;
	}
	SWCTLSTATIC : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hCA4 };
		option.weight = 1;
	}
	CGCTL : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hCB0 };
		option.weight = 1;
	}
	INITTMG0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hD00 };
		option.weight = 1;
	}
	PPT2CTRL0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF00 };
		option.weight = 1;
	}
	PPT2STAT0 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hF10 };
		option.weight = 1;
	}
	DDRCTL_VER_NUMBER : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFF8 };
		option.weight = 1;
	}
	DDRCTL_VER_TYPE : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFFC };
		option.weight = 1;
	}
endgroup
	function new(string name = "DWC_ddrctl_map_REGB_DDRC_CH0");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new
   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.MSTR0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MSTR0::type_id::create("MSTR0",,get_full_name());
      if(this.MSTR0.has_coverage(UVM_CVR_REG_BITS))
      	this.MSTR0.cg_bits.option.name = {get_name(), ".", "MSTR0_bits"};
      this.MSTR0.configure(this, null, "");
      this.MSTR0.build();
	  uvm_resource_db#(string)::set({"REG::", MSTR0.get_full_name()}, "accessType", "NONSECURE", this);
         this.MSTR0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_lpddr4", 1, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_lpddr5", 3, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_lpddr5x", 11, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_data_bus_width", 12, 2},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_burst_rdwr", 16, 5},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_active_ranks", 24, 2}
         });
      this.default_map.add_reg(this.MSTR0, `UVM_REG_ADDR_WIDTH'h0, "RW", 0);
		this.MSTR0_lpddr4 = this.MSTR0.lpddr4;
		this.lpddr4 = this.MSTR0.lpddr4;
		this.MSTR0_lpddr5 = this.MSTR0.lpddr5;
		this.lpddr5 = this.MSTR0.lpddr5;
		this.MSTR0_lpddr5x = this.MSTR0.lpddr5x;
		this.lpddr5x = this.MSTR0.lpddr5x;
		this.MSTR0_data_bus_width = this.MSTR0.data_bus_width;
		this.data_bus_width = this.MSTR0.data_bus_width;
		this.MSTR0_burst_rdwr = this.MSTR0.burst_rdwr;
		this.burst_rdwr = this.MSTR0.burst_rdwr;
		this.MSTR0_active_ranks = this.MSTR0.active_ranks;
		this.active_ranks = this.MSTR0.active_ranks;
      this.MSTR2 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MSTR2::type_id::create("MSTR2",,get_full_name());
      if(this.MSTR2.has_coverage(UVM_CVR_REG_BITS))
      	this.MSTR2.cg_bits.option.name = {get_name(), ".", "MSTR2_bits"};
      this.MSTR2.configure(this, null, "");
      this.MSTR2.build();
	  uvm_resource_db#(string)::set({"REG::", MSTR2.get_full_name()}, "accessType", "NONSECURE", this);
         this.MSTR2.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_target_frequency", 0, 2}
         });
      this.default_map.add_reg(this.MSTR2, `UVM_REG_ADDR_WIDTH'h8, "RW", 0);
		this.MSTR2_target_frequency = this.MSTR2.target_frequency;
		this.target_frequency = this.MSTR2.target_frequency;
      this.MSTR4 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MSTR4::type_id::create("MSTR4",,get_full_name());
      if(this.MSTR4.has_coverage(UVM_CVR_REG_BITS))
      	this.MSTR4.cg_bits.option.name = {get_name(), ".", "MSTR4_bits"};
      this.MSTR4.configure(this, null, "");
      this.MSTR4.build();
	  uvm_resource_db#(string)::set({"REG::", MSTR4.get_full_name()}, "accessType", "NONSECURE", this);
         this.MSTR4.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_wck_on", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_wck_suspend_en", 4, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ws_off_en", 8, 1}
         });
      this.default_map.add_reg(this.MSTR4, `UVM_REG_ADDR_WIDTH'h10, "RW", 0);
		this.MSTR4_wck_on = this.MSTR4.wck_on;
		this.wck_on = this.MSTR4.wck_on;
		this.MSTR4_wck_suspend_en = this.MSTR4.wck_suspend_en;
		this.wck_suspend_en = this.MSTR4.wck_suspend_en;
		this.MSTR4_ws_off_en = this.MSTR4.ws_off_en;
		this.ws_off_en = this.MSTR4.ws_off_en;
      this.STAT = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_STAT::type_id::create("STAT",,get_full_name());
      if(this.STAT.has_coverage(UVM_CVR_REG_BITS))
      	this.STAT.cg_bits.option.name = {get_name(), ".", "STAT_bits"};
      this.STAT.configure(this, null, "");
      this.STAT.build();
	  uvm_resource_db#(string)::set({"REG::", STAT.get_full_name()}, "accessType", "NONSECURE", this);
         this.STAT.add_hdl_path('{
            '{"ddrc_reg_operating_mode", 0, 3},
            '{"ddrc_reg_selfref_type", 4, 2},
            '{"ddrc_reg_selfref_state", 12, 3},
            '{"ddrc_reg_selfref_cam_not_empty", 16, 1}
         });
      this.default_map.add_reg(this.STAT, `UVM_REG_ADDR_WIDTH'h14, "RO", 0);
		this.STAT_operating_mode = this.STAT.operating_mode;
		this.operating_mode = this.STAT.operating_mode;
		this.STAT_selfref_type = this.STAT.selfref_type;
		this.selfref_type = this.STAT.selfref_type;
		this.STAT_selfref_state = this.STAT.selfref_state;
		this.selfref_state = this.STAT.selfref_state;
		this.STAT_selfref_cam_not_empty = this.STAT.selfref_cam_not_empty;
		this.selfref_cam_not_empty = this.STAT.selfref_cam_not_empty;
      this.MRCTRL0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRCTRL0::type_id::create("MRCTRL0",,get_full_name());
      if(this.MRCTRL0.has_coverage(UVM_CVR_REG_BITS))
      	this.MRCTRL0.cg_bits.option.name = {get_name(), ".", "MRCTRL0_bits"};
      this.MRCTRL0.configure(this, null, "");
      this.MRCTRL0.build();
	  uvm_resource_db#(bit)::set({"REG::", MRCTRL0.get_full_name()}, "NO_REG_BIT_BASH_TEST", 1, this);
	  uvm_resource_db#(string)::set({"REG::", MRCTRL0.get_full_name()}, "accessType", "NONSECURE", this);
         this.MRCTRL0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_mr_type", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_sw_init_int", 3, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_mr_rank", 4, 2},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_mr_addr", 12, 4},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_mrr_done_clr", 24, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dis_mrrw_trfc", 27, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ppr_en", 28, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ppr_pgmpst_en", 29, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_mr_wr", 31, 1}
         });
      this.default_map.add_reg(this.MRCTRL0, `UVM_REG_ADDR_WIDTH'h80, "RW", 0);
		this.MRCTRL0_mr_type = this.MRCTRL0.mr_type;
		this.mr_type = this.MRCTRL0.mr_type;
		this.MRCTRL0_sw_init_int = this.MRCTRL0.sw_init_int;
		this.sw_init_int = this.MRCTRL0.sw_init_int;
		this.MRCTRL0_mr_rank = this.MRCTRL0.mr_rank;
		this.mr_rank = this.MRCTRL0.mr_rank;
		this.MRCTRL0_mr_addr = this.MRCTRL0.mr_addr;
		this.mr_addr = this.MRCTRL0.mr_addr;
		this.MRCTRL0_mrr_done_clr = this.MRCTRL0.mrr_done_clr;
		this.mrr_done_clr = this.MRCTRL0.mrr_done_clr;
		this.MRCTRL0_dis_mrrw_trfc = this.MRCTRL0.dis_mrrw_trfc;
		this.dis_mrrw_trfc = this.MRCTRL0.dis_mrrw_trfc;
		this.MRCTRL0_ppr_en = this.MRCTRL0.ppr_en;
		this.ppr_en = this.MRCTRL0.ppr_en;
		this.MRCTRL0_ppr_pgmpst_en = this.MRCTRL0.ppr_pgmpst_en;
		this.ppr_pgmpst_en = this.MRCTRL0.ppr_pgmpst_en;
		this.MRCTRL0_mr_wr = this.MRCTRL0.mr_wr;
		this.mr_wr = this.MRCTRL0.mr_wr;
      this.MRCTRL1 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRCTRL1::type_id::create("MRCTRL1",,get_full_name());
      if(this.MRCTRL1.has_coverage(UVM_CVR_REG_BITS))
      	this.MRCTRL1.cg_bits.option.name = {get_name(), ".", "MRCTRL1_bits"};
      this.MRCTRL1.configure(this, null, "");
      this.MRCTRL1.build();
	  uvm_resource_db#(string)::set({"REG::", MRCTRL1.get_full_name()}, "accessType", "NONSECURE", this);
         this.MRCTRL1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_mr_data", 0, 18}
         });
      this.default_map.add_reg(this.MRCTRL1, `UVM_REG_ADDR_WIDTH'h84, "RW", 0);
		this.MRCTRL1_mr_data = this.MRCTRL1.mr_data;
		this.mr_data = this.MRCTRL1.mr_data;
      this.MRSTAT = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRSTAT::type_id::create("MRSTAT",,get_full_name());
      if(this.MRSTAT.has_coverage(UVM_CVR_REG_BITS))
      	this.MRSTAT.cg_bits.option.name = {get_name(), ".", "MRSTAT_bits"};
      this.MRSTAT.configure(this, null, "");
      this.MRSTAT.build();
	  uvm_resource_db#(string)::set({"REG::", MRSTAT.get_full_name()}, "accessType", "NONSECURE", this);
         this.MRSTAT.add_hdl_path('{
            '{"ddrc_reg_mr_wr_busy", 0, 1},
            '{"ddrc_reg_mrr_done", 16, 1},
            '{"ddrc_reg_ppr_done", 17, 1}
         });
      this.default_map.add_reg(this.MRSTAT, `UVM_REG_ADDR_WIDTH'h90, "RO", 0);
		this.MRSTAT_mr_wr_busy = this.MRSTAT.mr_wr_busy;
		this.mr_wr_busy = this.MRSTAT.mr_wr_busy;
		this.MRSTAT_mrr_done = this.MRSTAT.mrr_done;
		this.mrr_done = this.MRSTAT.mrr_done;
		this.MRSTAT_ppr_done = this.MRSTAT.ppr_done;
		this.ppr_done = this.MRSTAT.ppr_done;
      this.MRRDATA0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRRDATA0::type_id::create("MRRDATA0",,get_full_name());
      if(this.MRRDATA0.has_coverage(UVM_CVR_REG_BITS))
      	this.MRRDATA0.cg_bits.option.name = {get_name(), ".", "MRRDATA0_bits"};
      this.MRRDATA0.configure(this, null, "");
      this.MRRDATA0.build();
	  uvm_resource_db#(string)::set({"REG::", MRRDATA0.get_full_name()}, "accessType", "NONSECURE", this);
         this.MRRDATA0.add_hdl_path('{
            '{"ddrc_reg_mrr_data_lwr", 0, 32}
         });
      this.default_map.add_reg(this.MRRDATA0, `UVM_REG_ADDR_WIDTH'h94, "RO", 0);
		this.MRRDATA0_mrr_data_lwr = this.MRRDATA0.mrr_data_lwr;
		this.mrr_data_lwr = this.MRRDATA0.mrr_data_lwr;
      this.MRRDATA1 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_MRRDATA1::type_id::create("MRRDATA1",,get_full_name());
      if(this.MRRDATA1.has_coverage(UVM_CVR_REG_BITS))
      	this.MRRDATA1.cg_bits.option.name = {get_name(), ".", "MRRDATA1_bits"};
      this.MRRDATA1.configure(this, null, "");
      this.MRRDATA1.build();
	  uvm_resource_db#(string)::set({"REG::", MRRDATA1.get_full_name()}, "accessType", "NONSECURE", this);
         this.MRRDATA1.add_hdl_path('{
            '{"ddrc_reg_mrr_data_upr", 0, 32}
         });
      this.default_map.add_reg(this.MRRDATA1, `UVM_REG_ADDR_WIDTH'h98, "RO", 0);
		this.MRRDATA1_mrr_data_upr = this.MRRDATA1.mrr_data_upr;
		this.mrr_data_upr = this.MRRDATA1.mrr_data_upr;
      this.DERATECTL0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL0::type_id::create("DERATECTL0",,get_full_name());
      if(this.DERATECTL0.has_coverage(UVM_CVR_REG_BITS))
      	this.DERATECTL0.cg_bits.option.name = {get_name(), ".", "DERATECTL0_bits"};
      this.DERATECTL0.configure(this, null, "");
      this.DERATECTL0.build();
	  uvm_resource_db#(string)::set({"REG::", DERATECTL0.get_full_name()}, "accessType", "NONSECURE", this);
         this.DERATECTL0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_derate_enable", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_lpddr4_refresh_mode", 1, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_derate_mr4_pause_fc", 2, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dis_trefi_x6x8", 3, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dis_trefi_x0125", 4, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_use_slow_rm_in_low_temp", 5, 1}
         });
      this.default_map.add_reg(this.DERATECTL0, `UVM_REG_ADDR_WIDTH'h100, "RW", 0);
		this.DERATECTL0_derate_enable = this.DERATECTL0.derate_enable;
		this.derate_enable = this.DERATECTL0.derate_enable;
		this.DERATECTL0_lpddr4_refresh_mode = this.DERATECTL0.lpddr4_refresh_mode;
		this.lpddr4_refresh_mode = this.DERATECTL0.lpddr4_refresh_mode;
		this.DERATECTL0_derate_mr4_pause_fc = this.DERATECTL0.derate_mr4_pause_fc;
		this.derate_mr4_pause_fc = this.DERATECTL0.derate_mr4_pause_fc;
		this.DERATECTL0_dis_trefi_x6x8 = this.DERATECTL0.dis_trefi_x6x8;
		this.dis_trefi_x6x8 = this.DERATECTL0.dis_trefi_x6x8;
		this.DERATECTL0_dis_trefi_x0125 = this.DERATECTL0.dis_trefi_x0125;
		this.dis_trefi_x0125 = this.DERATECTL0.dis_trefi_x0125;
		this.DERATECTL0_use_slow_rm_in_low_temp = this.DERATECTL0.use_slow_rm_in_low_temp;
		this.use_slow_rm_in_low_temp = this.DERATECTL0.use_slow_rm_in_low_temp;
      this.DERATECTL1 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL1::type_id::create("DERATECTL1",,get_full_name());
      if(this.DERATECTL1.has_coverage(UVM_CVR_REG_BITS))
      	this.DERATECTL1.cg_bits.option.name = {get_name(), ".", "DERATECTL1_bits"};
      this.DERATECTL1.configure(this, null, "");
      this.DERATECTL1.build();
	  uvm_resource_db#(string)::set({"REG::", DERATECTL1.get_full_name()}, "accessType", "NONSECURE", this);
         this.DERATECTL1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_active_derate_byte_rank0", 0, 8}
         });
      this.default_map.add_reg(this.DERATECTL1, `UVM_REG_ADDR_WIDTH'h104, "RW", 0);
		this.DERATECTL1_active_derate_byte_rank0 = this.DERATECTL1.active_derate_byte_rank0;
		this.active_derate_byte_rank0 = this.DERATECTL1.active_derate_byte_rank0;
      this.DERATECTL2 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL2::type_id::create("DERATECTL2",,get_full_name());
      if(this.DERATECTL2.has_coverage(UVM_CVR_REG_BITS))
      	this.DERATECTL2.cg_bits.option.name = {get_name(), ".", "DERATECTL2_bits"};
      this.DERATECTL2.configure(this, null, "");
      this.DERATECTL2.build();
	  uvm_resource_db#(string)::set({"REG::", DERATECTL2.get_full_name()}, "accessType", "NONSECURE", this);
         this.DERATECTL2.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_active_derate_byte_rank1", 0, 8}
         });
      this.default_map.add_reg(this.DERATECTL2, `UVM_REG_ADDR_WIDTH'h108, "RW", 0);
		this.DERATECTL2_active_derate_byte_rank1 = this.DERATECTL2.active_derate_byte_rank1;
		this.active_derate_byte_rank1 = this.DERATECTL2.active_derate_byte_rank1;
      this.DERATECTL5 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL5::type_id::create("DERATECTL5",,get_full_name());
      if(this.DERATECTL5.has_coverage(UVM_CVR_REG_BITS))
      	this.DERATECTL5.cg_bits.option.name = {get_name(), ".", "DERATECTL5_bits"};
      this.DERATECTL5.configure(this, null, "");
      this.DERATECTL5.build();
	  uvm_resource_db#(bit)::set({"REG::", DERATECTL5.get_full_name()}, "NO_REG_BIT_BASH_TEST", 1, this);
	  uvm_resource_db#(string)::set({"REG::", DERATECTL5.get_full_name()}, "accessType", "NONSECURE", this);
         this.DERATECTL5.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_derate_temp_limit_intr_en", 0, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_derate_temp_limit_intr_clr", 1, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_derate_temp_limit_intr_force", 2, 1}
         });
      this.default_map.add_reg(this.DERATECTL5, `UVM_REG_ADDR_WIDTH'h114, "RW", 0);
		this.DERATECTL5_derate_temp_limit_intr_en = this.DERATECTL5.derate_temp_limit_intr_en;
		this.derate_temp_limit_intr_en = this.DERATECTL5.derate_temp_limit_intr_en;
		this.DERATECTL5_derate_temp_limit_intr_clr = this.DERATECTL5.derate_temp_limit_intr_clr;
		this.derate_temp_limit_intr_clr = this.DERATECTL5.derate_temp_limit_intr_clr;
		this.DERATECTL5_derate_temp_limit_intr_force = this.DERATECTL5.derate_temp_limit_intr_force;
		this.derate_temp_limit_intr_force = this.DERATECTL5.derate_temp_limit_intr_force;
      this.DERATECTL6 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATECTL6::type_id::create("DERATECTL6",,get_full_name());
      if(this.DERATECTL6.has_coverage(UVM_CVR_REG_BITS))
      	this.DERATECTL6.cg_bits.option.name = {get_name(), ".", "DERATECTL6_bits"};
      this.DERATECTL6.configure(this, null, "");
      this.DERATECTL6.build();
	  uvm_resource_db#(string)::set({"REG::", DERATECTL6.get_full_name()}, "accessType", "NONSECURE", this);
         this.DERATECTL6.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_derate_mr4_tuf_dis", 0, 1}
         });
      this.default_map.add_reg(this.DERATECTL6, `UVM_REG_ADDR_WIDTH'h118, "RW", 0);
		this.DERATECTL6_derate_mr4_tuf_dis = this.DERATECTL6.derate_mr4_tuf_dis;
		this.derate_mr4_tuf_dis = this.DERATECTL6.derate_mr4_tuf_dis;
      this.DERATESTAT0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATESTAT0::type_id::create("DERATESTAT0",,get_full_name());
      if(this.DERATESTAT0.has_coverage(UVM_CVR_REG_BITS))
      	this.DERATESTAT0.cg_bits.option.name = {get_name(), ".", "DERATESTAT0_bits"};
      this.DERATESTAT0.configure(this, null, "");
      this.DERATESTAT0.build();
	  uvm_resource_db#(bit)::set({"REG::", DERATESTAT0.get_full_name()}, "NO_REG_BIT_BASH_TEST", 1, this);
	  uvm_resource_db#(string)::set({"REG::", DERATESTAT0.get_full_name()}, "accessType", "NONSECURE", this);
         this.DERATESTAT0.add_hdl_path('{
            '{"ddrc_reg_derate_temp_limit_intr", 0, 1}
         });
      this.default_map.add_reg(this.DERATESTAT0, `UVM_REG_ADDR_WIDTH'h120, "RO", 0);
		this.DERATESTAT0_derate_temp_limit_intr = this.DERATESTAT0.derate_temp_limit_intr;
		this.derate_temp_limit_intr = this.DERATESTAT0.derate_temp_limit_intr;
      this.DERATEDBGCTL = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATEDBGCTL::type_id::create("DERATEDBGCTL",,get_full_name());
      if(this.DERATEDBGCTL.has_coverage(UVM_CVR_REG_BITS))
      	this.DERATEDBGCTL.cg_bits.option.name = {get_name(), ".", "DERATEDBGCTL_bits"};
      this.DERATEDBGCTL.configure(this, null, "");
      this.DERATEDBGCTL.build();
	  uvm_resource_db#(string)::set({"REG::", DERATEDBGCTL.get_full_name()}, "accessType", "NONSECURE", this);
         this.DERATEDBGCTL.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dbg_mr4_rank_sel", 4, 2}
         });
      this.default_map.add_reg(this.DERATEDBGCTL, `UVM_REG_ADDR_WIDTH'h128, "RW", 0);
		this.DERATEDBGCTL_dbg_mr4_rank_sel = this.DERATEDBGCTL.dbg_mr4_rank_sel;
		this.dbg_mr4_rank_sel = this.DERATEDBGCTL.dbg_mr4_rank_sel;
      this.DERATEDBGSTAT = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DERATEDBGSTAT::type_id::create("DERATEDBGSTAT",,get_full_name());
      if(this.DERATEDBGSTAT.has_coverage(UVM_CVR_REG_BITS))
      	this.DERATEDBGSTAT.cg_bits.option.name = {get_name(), ".", "DERATEDBGSTAT_bits"};
      this.DERATEDBGSTAT.configure(this, null, "");
      this.DERATEDBGSTAT.build();
	  uvm_resource_db#(string)::set({"REG::", DERATEDBGSTAT.get_full_name()}, "accessType", "NONSECURE", this);
         this.DERATEDBGSTAT.add_hdl_path('{
            '{"ddrc_reg_dbg_mr4_byte0", 0, 8},
            '{"ddrc_reg_dbg_mr4_byte1", 8, 8},
            '{"ddrc_reg_dbg_mr4_byte2", 16, 8},
            '{"ddrc_reg_dbg_mr4_byte3", 24, 8}
         });
      this.default_map.add_reg(this.DERATEDBGSTAT, `UVM_REG_ADDR_WIDTH'h12C, "RO", 0);
		this.DERATEDBGSTAT_dbg_mr4_byte0 = this.DERATEDBGSTAT.dbg_mr4_byte0;
		this.dbg_mr4_byte0 = this.DERATEDBGSTAT.dbg_mr4_byte0;
		this.DERATEDBGSTAT_dbg_mr4_byte1 = this.DERATEDBGSTAT.dbg_mr4_byte1;
		this.dbg_mr4_byte1 = this.DERATEDBGSTAT.dbg_mr4_byte1;
		this.DERATEDBGSTAT_dbg_mr4_byte2 = this.DERATEDBGSTAT.dbg_mr4_byte2;
		this.dbg_mr4_byte2 = this.DERATEDBGSTAT.dbg_mr4_byte2;
		this.DERATEDBGSTAT_dbg_mr4_byte3 = this.DERATEDBGSTAT.dbg_mr4_byte3;
		this.dbg_mr4_byte3 = this.DERATEDBGSTAT.dbg_mr4_byte3;
      this.PWRCTL = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_PWRCTL::type_id::create("PWRCTL",,get_full_name());
      if(this.PWRCTL.has_coverage(UVM_CVR_REG_BITS))
      	this.PWRCTL.cg_bits.option.name = {get_name(), ".", "PWRCTL_bits"};
      this.PWRCTL.configure(this, null, "");
      this.PWRCTL.build();
	  uvm_resource_db#(string)::set({"REG::", PWRCTL.get_full_name()}, "accessType", "NONSECURE", this);
         this.PWRCTL.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_selfref_en", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_powerdown_en", 4, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_en_dfi_dram_clk_disable", 9, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_selfref_sw", 11, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_stay_in_selfref", 15, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dis_cam_drain_selfref", 16, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_lpddr4_sr_allowed", 17, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dsm_en", 18, 1}
         });
      this.default_map.add_reg(this.PWRCTL, `UVM_REG_ADDR_WIDTH'h180, "RW", 0);
		this.PWRCTL_selfref_en = this.PWRCTL.selfref_en;
		this.selfref_en = this.PWRCTL.selfref_en;
		this.PWRCTL_powerdown_en = this.PWRCTL.powerdown_en;
		this.powerdown_en = this.PWRCTL.powerdown_en;
		this.PWRCTL_en_dfi_dram_clk_disable = this.PWRCTL.en_dfi_dram_clk_disable;
		this.en_dfi_dram_clk_disable = this.PWRCTL.en_dfi_dram_clk_disable;
		this.PWRCTL_selfref_sw = this.PWRCTL.selfref_sw;
		this.selfref_sw = this.PWRCTL.selfref_sw;
		this.PWRCTL_stay_in_selfref = this.PWRCTL.stay_in_selfref;
		this.stay_in_selfref = this.PWRCTL.stay_in_selfref;
		this.PWRCTL_dis_cam_drain_selfref = this.PWRCTL.dis_cam_drain_selfref;
		this.dis_cam_drain_selfref = this.PWRCTL.dis_cam_drain_selfref;
		this.PWRCTL_lpddr4_sr_allowed = this.PWRCTL.lpddr4_sr_allowed;
		this.lpddr4_sr_allowed = this.PWRCTL.lpddr4_sr_allowed;
		this.PWRCTL_dsm_en = this.PWRCTL.dsm_en;
		this.dsm_en = this.PWRCTL.dsm_en;
      this.HWLPCTL = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_HWLPCTL::type_id::create("HWLPCTL",,get_full_name());
      if(this.HWLPCTL.has_coverage(UVM_CVR_REG_BITS))
      	this.HWLPCTL.cg_bits.option.name = {get_name(), ".", "HWLPCTL_bits"};
      this.HWLPCTL.configure(this, null, "");
      this.HWLPCTL.build();
	  uvm_resource_db#(bit)::set({"REG::", HWLPCTL.get_full_name()}, "NO_REG_BIT_BASH_TEST", 1, this);
	  uvm_resource_db#(string)::set({"REG::", HWLPCTL.get_full_name()}, "accessType", "NONSECURE", this);
         this.HWLPCTL.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_hw_lp_en", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_hw_lp_exit_idle_en", 1, 1}
         });
      this.default_map.add_reg(this.HWLPCTL, `UVM_REG_ADDR_WIDTH'h184, "RW", 0);
		this.HWLPCTL_hw_lp_en = this.HWLPCTL.hw_lp_en;
		this.hw_lp_en = this.HWLPCTL.hw_lp_en;
		this.HWLPCTL_hw_lp_exit_idle_en = this.HWLPCTL.hw_lp_exit_idle_en;
		this.hw_lp_exit_idle_en = this.HWLPCTL.hw_lp_exit_idle_en;
      this.CLKGATECTL = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_CLKGATECTL::type_id::create("CLKGATECTL",,get_full_name());
      if(this.CLKGATECTL.has_coverage(UVM_CVR_REG_BITS))
      	this.CLKGATECTL.cg_bits.option.name = {get_name(), ".", "CLKGATECTL_bits"};
      this.CLKGATECTL.configure(this, null, "");
      this.CLKGATECTL.build();
	  uvm_resource_db#(string)::set({"REG::", CLKGATECTL.get_full_name()}, "accessType", "NONSECURE", this);
         this.CLKGATECTL.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_bsm_clk_on", 0, 6}
         });
      this.default_map.add_reg(this.CLKGATECTL, `UVM_REG_ADDR_WIDTH'h18C, "RW", 0);
		this.CLKGATECTL_bsm_clk_on = this.CLKGATECTL.bsm_clk_on;
		this.bsm_clk_on = this.CLKGATECTL.bsm_clk_on;
      this.RFSHMOD0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFSHMOD0::type_id::create("RFSHMOD0",,get_full_name());
      if(this.RFSHMOD0.has_coverage(UVM_CVR_REG_BITS))
      	this.RFSHMOD0.cg_bits.option.name = {get_name(), ".", "RFSHMOD0_bits"};
      this.RFSHMOD0.configure(this, null, "");
      this.RFSHMOD0.build();
	  uvm_resource_db#(string)::set({"REG::", RFSHMOD0.get_full_name()}, "accessType", "NONSECURE", this);
         this.RFSHMOD0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_refresh_burst", 0, 6},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_auto_refab_en", 6, 2},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_per_bank_refresh", 8, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_per_bank_refresh_opt_en", 9, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_fixed_crit_refpb_bank_en", 24, 1}
         });
      this.default_map.add_reg(this.RFSHMOD0, `UVM_REG_ADDR_WIDTH'h200, "RW", 0);
		this.RFSHMOD0_refresh_burst = this.RFSHMOD0.refresh_burst;
		this.refresh_burst = this.RFSHMOD0.refresh_burst;
		this.RFSHMOD0_auto_refab_en = this.RFSHMOD0.auto_refab_en;
		this.auto_refab_en = this.RFSHMOD0.auto_refab_en;
		this.RFSHMOD0_per_bank_refresh = this.RFSHMOD0.per_bank_refresh;
		this.per_bank_refresh = this.RFSHMOD0.per_bank_refresh;
		this.RFSHMOD0_per_bank_refresh_opt_en = this.RFSHMOD0.per_bank_refresh_opt_en;
		this.per_bank_refresh_opt_en = this.RFSHMOD0.per_bank_refresh_opt_en;
		this.RFSHMOD0_fixed_crit_refpb_bank_en = this.RFSHMOD0.fixed_crit_refpb_bank_en;
		this.fixed_crit_refpb_bank_en = this.RFSHMOD0.fixed_crit_refpb_bank_en;
      this.RFSHCTL0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFSHCTL0::type_id::create("RFSHCTL0",,get_full_name());
      if(this.RFSHCTL0.has_coverage(UVM_CVR_REG_BITS))
      	this.RFSHCTL0.cg_bits.option.name = {get_name(), ".", "RFSHCTL0_bits"};
      this.RFSHCTL0.configure(this, null, "");
      this.RFSHCTL0.build();
	  uvm_resource_db#(string)::set({"REG::", RFSHCTL0.get_full_name()}, "accessType", "NONSECURE", this);
         this.RFSHCTL0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dis_auto_refresh", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_refresh_update_level", 4, 1}
         });
      this.default_map.add_reg(this.RFSHCTL0, `UVM_REG_ADDR_WIDTH'h208, "RW", 0);
		this.RFSHCTL0_dis_auto_refresh = this.RFSHCTL0.dis_auto_refresh;
		this.dis_auto_refresh = this.RFSHCTL0.dis_auto_refresh;
		this.RFSHCTL0_refresh_update_level = this.RFSHCTL0.refresh_update_level;
		this.refresh_update_level = this.RFSHCTL0.refresh_update_level;
      this.RFMMOD0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFMMOD0::type_id::create("RFMMOD0",,get_full_name());
      if(this.RFMMOD0.has_coverage(UVM_CVR_REG_BITS))
      	this.RFMMOD0.cg_bits.option.name = {get_name(), ".", "RFMMOD0_bits"};
      this.RFMMOD0.configure(this, null, "");
      this.RFMMOD0.build();
	  uvm_resource_db#(string)::set({"REG::", RFMMOD0.get_full_name()}, "accessType", "NONSECURE", this);
         this.RFMMOD0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rfm_en", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rfmsbc", 4, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_raaimt", 8, 5},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_raamult", 16, 2},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_raadec", 18, 2},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rfmth_rm_thr", 24, 5}
         });
      this.default_map.add_reg(this.RFMMOD0, `UVM_REG_ADDR_WIDTH'h220, "RW", 0);
		this.RFMMOD0_rfm_en = this.RFMMOD0.rfm_en;
		this.rfm_en = this.RFMMOD0.rfm_en;
		this.RFMMOD0_rfmsbc = this.RFMMOD0.rfmsbc;
		this.rfmsbc = this.RFMMOD0.rfmsbc;
		this.RFMMOD0_raaimt = this.RFMMOD0.raaimt;
		this.raaimt = this.RFMMOD0.raaimt;
		this.RFMMOD0_raamult = this.RFMMOD0.raamult;
		this.raamult = this.RFMMOD0.raamult;
		this.RFMMOD0_raadec = this.RFMMOD0.raadec;
		this.raadec = this.RFMMOD0.raadec;
		this.RFMMOD0_rfmth_rm_thr = this.RFMMOD0.rfmth_rm_thr;
		this.rfmth_rm_thr = this.RFMMOD0.rfmth_rm_thr;
      this.RFMMOD1 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFMMOD1::type_id::create("RFMMOD1",,get_full_name());
      if(this.RFMMOD1.has_coverage(UVM_CVR_REG_BITS))
      	this.RFMMOD1.cg_bits.option.name = {get_name(), ".", "RFMMOD1_bits"};
      this.RFMMOD1.configure(this, null, "");
      this.RFMMOD1.build();
	  uvm_resource_db#(string)::set({"REG::", RFMMOD1.get_full_name()}, "accessType", "NONSECURE", this);
         this.RFMMOD1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_init_raa_cnt", 0, 11}
         });
      this.default_map.add_reg(this.RFMMOD1, `UVM_REG_ADDR_WIDTH'h224, "RW", 0);
		this.RFMMOD1_init_raa_cnt = this.RFMMOD1.init_raa_cnt;
		this.init_raa_cnt = this.RFMMOD1.init_raa_cnt;
      this.RFMCTL = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFMCTL::type_id::create("RFMCTL",,get_full_name());
      if(this.RFMCTL.has_coverage(UVM_CVR_REG_BITS))
      	this.RFMCTL.cg_bits.option.name = {get_name(), ".", "RFMCTL_bits"};
      this.RFMCTL.configure(this, null, "");
      this.RFMCTL.build();
	  uvm_resource_db#(string)::set({"REG::", RFMCTL.get_full_name()}, "accessType", "NONSECURE", this);
         this.RFMCTL.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dbg_raa_rank", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dbg_raa_bg_bank", 4, 4}
         });
      this.default_map.add_reg(this.RFMCTL, `UVM_REG_ADDR_WIDTH'h228, "RW", 0);
		this.RFMCTL_dbg_raa_rank = this.RFMCTL.dbg_raa_rank;
		this.dbg_raa_rank = this.RFMCTL.dbg_raa_rank;
		this.RFMCTL_dbg_raa_bg_bank = this.RFMCTL.dbg_raa_bg_bank;
		this.dbg_raa_bg_bank = this.RFMCTL.dbg_raa_bg_bank;
      this.RFMSTAT = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RFMSTAT::type_id::create("RFMSTAT",,get_full_name());
      if(this.RFMSTAT.has_coverage(UVM_CVR_REG_BITS))
      	this.RFMSTAT.cg_bits.option.name = {get_name(), ".", "RFMSTAT_bits"};
      this.RFMSTAT.configure(this, null, "");
      this.RFMSTAT.build();
	  uvm_resource_db#(string)::set({"REG::", RFMSTAT.get_full_name()}, "accessType", "NONSECURE", this);
         this.RFMSTAT.add_hdl_path('{
            '{"ddrc_reg_rank_raa_cnt_gt0", 0, 2},
            '{"ddrc_reg_dbg_raa_cnt", 16, 11}
         });
      this.default_map.add_reg(this.RFMSTAT, `UVM_REG_ADDR_WIDTH'h22C, "RO", 0);
		this.RFMSTAT_rank_raa_cnt_gt0 = this.RFMSTAT.rank_raa_cnt_gt0;
		this.rank_raa_cnt_gt0 = this.RFMSTAT.rank_raa_cnt_gt0;
		this.RFMSTAT_dbg_raa_cnt = this.RFMSTAT.dbg_raa_cnt;
		this.dbg_raa_cnt = this.RFMSTAT.dbg_raa_cnt;
      this.ZQCTL0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ZQCTL0::type_id::create("ZQCTL0",,get_full_name());
      if(this.ZQCTL0.has_coverage(UVM_CVR_REG_BITS))
      	this.ZQCTL0.cg_bits.option.name = {get_name(), ".", "ZQCTL0_bits"};
      this.ZQCTL0.configure(this, null, "");
      this.ZQCTL0.build();
	  uvm_resource_db#(string)::set({"REG::", ZQCTL0.get_full_name()}, "accessType", "NONSECURE", this);
         this.ZQCTL0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_zq_resistor_shared", 29, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dis_auto_zq", 31, 1}
         });
      this.default_map.add_reg(this.ZQCTL0, `UVM_REG_ADDR_WIDTH'h280, "RW", 0);
		this.ZQCTL0_zq_resistor_shared = this.ZQCTL0.zq_resistor_shared;
		this.zq_resistor_shared = this.ZQCTL0.zq_resistor_shared;
		this.ZQCTL0_dis_auto_zq = this.ZQCTL0.dis_auto_zq;
		this.dis_auto_zq = this.ZQCTL0.dis_auto_zq;
      this.ZQCTL1 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ZQCTL1::type_id::create("ZQCTL1",,get_full_name());
      if(this.ZQCTL1.has_coverage(UVM_CVR_REG_BITS))
      	this.ZQCTL1.cg_bits.option.name = {get_name(), ".", "ZQCTL1_bits"};
      this.ZQCTL1.configure(this, null, "");
      this.ZQCTL1.build();
	  uvm_resource_db#(bit)::set({"REG::", ZQCTL1.get_full_name()}, "NO_REG_BIT_BASH_TEST", 1, this);
	  uvm_resource_db#(string)::set({"REG::", ZQCTL1.get_full_name()}, "accessType", "NONSECURE", this);
         this.ZQCTL1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_zq_reset", 0, 1}
         });
      this.default_map.add_reg(this.ZQCTL1, `UVM_REG_ADDR_WIDTH'h284, "RW", 0);
		this.ZQCTL1_zq_reset = this.ZQCTL1.zq_reset;
		this.zq_reset = this.ZQCTL1.zq_reset;
      this.ZQCTL2 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ZQCTL2::type_id::create("ZQCTL2",,get_full_name());
      if(this.ZQCTL2.has_coverage(UVM_CVR_REG_BITS))
      	this.ZQCTL2.cg_bits.option.name = {get_name(), ".", "ZQCTL2_bits"};
      this.ZQCTL2.configure(this, null, "");
      this.ZQCTL2.build();
	  uvm_resource_db#(string)::set({"REG::", ZQCTL2.get_full_name()}, "accessType", "NONSECURE", this);
         this.ZQCTL2.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_dis_srx_zqcl", 0, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_dis_srx_zqcl_hwffc", 1, 1}
         });
      this.default_map.add_reg(this.ZQCTL2, `UVM_REG_ADDR_WIDTH'h288, "RW", 0);
		this.ZQCTL2_dis_srx_zqcl = this.ZQCTL2.dis_srx_zqcl;
		this.dis_srx_zqcl = this.ZQCTL2.dis_srx_zqcl;
		this.ZQCTL2_dis_srx_zqcl_hwffc = this.ZQCTL2.dis_srx_zqcl_hwffc;
		this.dis_srx_zqcl_hwffc = this.ZQCTL2.dis_srx_zqcl_hwffc;
      this.ZQSTAT = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ZQSTAT::type_id::create("ZQSTAT",,get_full_name());
      if(this.ZQSTAT.has_coverage(UVM_CVR_REG_BITS))
      	this.ZQSTAT.cg_bits.option.name = {get_name(), ".", "ZQSTAT_bits"};
      this.ZQSTAT.configure(this, null, "");
      this.ZQSTAT.build();
	  uvm_resource_db#(string)::set({"REG::", ZQSTAT.get_full_name()}, "accessType", "NONSECURE", this);
         this.ZQSTAT.add_hdl_path('{
            '{"ddrc_reg_zq_reset_busy", 0, 1}
         });
      this.default_map.add_reg(this.ZQSTAT, `UVM_REG_ADDR_WIDTH'h28C, "RO", 0);
		this.ZQSTAT_zq_reset_busy = this.ZQSTAT.zq_reset_busy;
		this.zq_reset_busy = this.ZQSTAT.zq_reset_busy;
      this.DQSOSCRUNTIME = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DQSOSCRUNTIME::type_id::create("DQSOSCRUNTIME",,get_full_name());
      if(this.DQSOSCRUNTIME.has_coverage(UVM_CVR_REG_BITS))
      	this.DQSOSCRUNTIME.cg_bits.option.name = {get_name(), ".", "DQSOSCRUNTIME_bits"};
      this.DQSOSCRUNTIME.configure(this, null, "");
      this.DQSOSCRUNTIME.build();
	  uvm_resource_db#(string)::set({"REG::", DQSOSCRUNTIME.get_full_name()}, "accessType", "NONSECURE", this);
         this.DQSOSCRUNTIME.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_dqsosc_runtime", 0, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_wck2dqo_runtime", 16, 8}
         });
      this.default_map.add_reg(this.DQSOSCRUNTIME, `UVM_REG_ADDR_WIDTH'h300, "RW", 0);
		this.DQSOSCRUNTIME_dqsosc_runtime = this.DQSOSCRUNTIME.dqsosc_runtime;
		this.dqsosc_runtime = this.DQSOSCRUNTIME.dqsosc_runtime;
		this.DQSOSCRUNTIME_wck2dqo_runtime = this.DQSOSCRUNTIME.wck2dqo_runtime;
		this.wck2dqo_runtime = this.DQSOSCRUNTIME.wck2dqo_runtime;
      this.DQSOSCSTAT0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DQSOSCSTAT0::type_id::create("DQSOSCSTAT0",,get_full_name());
      if(this.DQSOSCSTAT0.has_coverage(UVM_CVR_REG_BITS))
      	this.DQSOSCSTAT0.cg_bits.option.name = {get_name(), ".", "DQSOSCSTAT0_bits"};
      this.DQSOSCSTAT0.configure(this, null, "");
      this.DQSOSCSTAT0.build();
	  uvm_resource_db#(string)::set({"REG::", DQSOSCSTAT0.get_full_name()}, "accessType", "NONSECURE", this);
         this.DQSOSCSTAT0.add_hdl_path('{
            '{"ddrc_reg_dqsosc_state", 0, 3},
            '{"ddrc_reg_dqsosc_per_rank_stat", 4, 2}
         });
      this.default_map.add_reg(this.DQSOSCSTAT0, `UVM_REG_ADDR_WIDTH'h304, "RO", 0);
		this.DQSOSCSTAT0_dqsosc_state = this.DQSOSCSTAT0.dqsosc_state;
		this.dqsosc_state = this.DQSOSCSTAT0.dqsosc_state;
		this.DQSOSCSTAT0_dqsosc_per_rank_stat = this.DQSOSCSTAT0.dqsosc_per_rank_stat;
		this.dqsosc_per_rank_stat = this.DQSOSCSTAT0.dqsosc_per_rank_stat;
      this.DQSOSCCFG0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DQSOSCCFG0::type_id::create("DQSOSCCFG0",,get_full_name());
      if(this.DQSOSCCFG0.has_coverage(UVM_CVR_REG_BITS))
      	this.DQSOSCCFG0.cg_bits.option.name = {get_name(), ".", "DQSOSCCFG0_bits"};
      this.DQSOSCCFG0.configure(this, null, "");
      this.DQSOSCCFG0.build();
	  uvm_resource_db#(string)::set({"REG::", DQSOSCCFG0.get_full_name()}, "accessType", "NONSECURE", this);
         this.DQSOSCCFG0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_dis_dqsosc_srx", 0, 1}
         });
      this.default_map.add_reg(this.DQSOSCCFG0, `UVM_REG_ADDR_WIDTH'h308, "RW", 0);
		this.DQSOSCCFG0_dis_dqsosc_srx = this.DQSOSCCFG0.dis_dqsosc_srx;
		this.dis_dqsosc_srx = this.DQSOSCCFG0.dis_dqsosc_srx;
      this.SCHED0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED0::type_id::create("SCHED0",,get_full_name());
      if(this.SCHED0.has_coverage(UVM_CVR_REG_BITS))
      	this.SCHED0.cg_bits.option.name = {get_name(), ".", "SCHED0_bits"};
      this.SCHED0.configure(this, null, "");
      this.SCHED0.build();
	  uvm_resource_db#(string)::set({"REG::", SCHED0.get_full_name()}, "accessType", "NONSECURE", this);
         this.SCHED0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_dis_opt_wrecc_collision_flush", 0, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_prefer_write", 1, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_pageclose", 2, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_opt_wrcam_fill_level", 4, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_dis_opt_ntt_by_act", 5, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_dis_opt_ntt_by_pre", 6, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_autopre_rmw", 7, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_lpr_num_entries", 8, 6},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_lpddr4_opt_act_timing", 15, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_lpddr5_opt_act_timing", 16, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_w_starve_free_running", 24, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_opt_act_lat", 27, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_prefer_read", 29, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_dis_speculative_act", 30, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_opt_vprw_sch", 31, 1}
         });
      this.default_map.add_reg(this.SCHED0, `UVM_REG_ADDR_WIDTH'h380, "RW", 0);
		this.SCHED0_dis_opt_wrecc_collision_flush = this.SCHED0.dis_opt_wrecc_collision_flush;
		this.dis_opt_wrecc_collision_flush = this.SCHED0.dis_opt_wrecc_collision_flush;
		this.SCHED0_prefer_write = this.SCHED0.prefer_write;
		this.prefer_write = this.SCHED0.prefer_write;
		this.SCHED0_pageclose = this.SCHED0.pageclose;
		this.pageclose = this.SCHED0.pageclose;
		this.SCHED0_opt_wrcam_fill_level = this.SCHED0.opt_wrcam_fill_level;
		this.opt_wrcam_fill_level = this.SCHED0.opt_wrcam_fill_level;
		this.SCHED0_dis_opt_ntt_by_act = this.SCHED0.dis_opt_ntt_by_act;
		this.dis_opt_ntt_by_act = this.SCHED0.dis_opt_ntt_by_act;
		this.SCHED0_dis_opt_ntt_by_pre = this.SCHED0.dis_opt_ntt_by_pre;
		this.dis_opt_ntt_by_pre = this.SCHED0.dis_opt_ntt_by_pre;
		this.SCHED0_autopre_rmw = this.SCHED0.autopre_rmw;
		this.autopre_rmw = this.SCHED0.autopre_rmw;
		this.SCHED0_lpr_num_entries = this.SCHED0.lpr_num_entries;
		this.lpr_num_entries = this.SCHED0.lpr_num_entries;
		this.SCHED0_lpddr4_opt_act_timing = this.SCHED0.lpddr4_opt_act_timing;
		this.lpddr4_opt_act_timing = this.SCHED0.lpddr4_opt_act_timing;
		this.SCHED0_lpddr5_opt_act_timing = this.SCHED0.lpddr5_opt_act_timing;
		this.lpddr5_opt_act_timing = this.SCHED0.lpddr5_opt_act_timing;
		this.SCHED0_w_starve_free_running = this.SCHED0.w_starve_free_running;
		this.w_starve_free_running = this.SCHED0.w_starve_free_running;
		this.SCHED0_opt_act_lat = this.SCHED0.opt_act_lat;
		this.opt_act_lat = this.SCHED0.opt_act_lat;
		this.SCHED0_prefer_read = this.SCHED0.prefer_read;
		this.prefer_read = this.SCHED0.prefer_read;
		this.SCHED0_dis_speculative_act = this.SCHED0.dis_speculative_act;
		this.dis_speculative_act = this.SCHED0.dis_speculative_act;
		this.SCHED0_opt_vprw_sch = this.SCHED0.opt_vprw_sch;
		this.opt_vprw_sch = this.SCHED0.opt_vprw_sch;
      this.SCHED1 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED1::type_id::create("SCHED1",,get_full_name());
      if(this.SCHED1.has_coverage(UVM_CVR_REG_BITS))
      	this.SCHED1.cg_bits.option.name = {get_name(), ".", "SCHED1_bits"};
      this.SCHED1.configure(this, null, "");
      this.SCHED1.build();
	  uvm_resource_db#(string)::set({"REG::", SCHED1.get_full_name()}, "accessType", "NONSECURE", this);
         this.SCHED1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_delay_switch_write", 12, 4},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_visible_window_limit_wr", 16, 3},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_visible_window_limit_rd", 20, 3},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_page_hit_limit_wr", 24, 3},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_page_hit_limit_rd", 28, 3},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_opt_hit_gt_hpr", 31, 1}
         });
      this.default_map.add_reg(this.SCHED1, `UVM_REG_ADDR_WIDTH'h384, "RW", 0);
		this.SCHED1_delay_switch_write = this.SCHED1.delay_switch_write;
		this.delay_switch_write = this.SCHED1.delay_switch_write;
		this.SCHED1_visible_window_limit_wr = this.SCHED1.visible_window_limit_wr;
		this.visible_window_limit_wr = this.SCHED1.visible_window_limit_wr;
		this.SCHED1_visible_window_limit_rd = this.SCHED1.visible_window_limit_rd;
		this.visible_window_limit_rd = this.SCHED1.visible_window_limit_rd;
		this.SCHED1_page_hit_limit_wr = this.SCHED1.page_hit_limit_wr;
		this.page_hit_limit_wr = this.SCHED1.page_hit_limit_wr;
		this.SCHED1_page_hit_limit_rd = this.SCHED1.page_hit_limit_rd;
		this.page_hit_limit_rd = this.SCHED1.page_hit_limit_rd;
		this.SCHED1_opt_hit_gt_hpr = this.SCHED1.opt_hit_gt_hpr;
		this.opt_hit_gt_hpr = this.SCHED1.opt_hit_gt_hpr;
      this.SCHED3 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED3::type_id::create("SCHED3",,get_full_name());
      if(this.SCHED3.has_coverage(UVM_CVR_REG_BITS))
      	this.SCHED3.cg_bits.option.name = {get_name(), ".", "SCHED3_bits"};
      this.SCHED3.configure(this, null, "");
      this.SCHED3.build();
	  uvm_resource_db#(string)::set({"REG::", SCHED3.get_full_name()}, "accessType", "NONSECURE", this);
         this.SCHED3.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_wrcam_lowthresh", 0, 6},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_wrcam_highthresh", 8, 6},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_wr_pghit_num_thresh", 16, 6},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_rd_pghit_num_thresh", 24, 6}
         });
      this.default_map.add_reg(this.SCHED3, `UVM_REG_ADDR_WIDTH'h38C, "RW", 0);
		this.SCHED3_wrcam_lowthresh = this.SCHED3.wrcam_lowthresh;
		this.wrcam_lowthresh = this.SCHED3.wrcam_lowthresh;
		this.SCHED3_wrcam_highthresh = this.SCHED3.wrcam_highthresh;
		this.wrcam_highthresh = this.SCHED3.wrcam_highthresh;
		this.SCHED3_wr_pghit_num_thresh = this.SCHED3.wr_pghit_num_thresh;
		this.wr_pghit_num_thresh = this.SCHED3.wr_pghit_num_thresh;
		this.SCHED3_rd_pghit_num_thresh = this.SCHED3.rd_pghit_num_thresh;
		this.rd_pghit_num_thresh = this.SCHED3.rd_pghit_num_thresh;
      this.SCHED4 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED4::type_id::create("SCHED4",,get_full_name());
      if(this.SCHED4.has_coverage(UVM_CVR_REG_BITS))
      	this.SCHED4.cg_bits.option.name = {get_name(), ".", "SCHED4_bits"};
      this.SCHED4.configure(this, null, "");
      this.SCHED4.build();
	  uvm_resource_db#(string)::set({"REG::", SCHED4.get_full_name()}, "accessType", "NONSECURE", this);
         this.SCHED4.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_rd_act_idle_gap", 0, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_wr_act_idle_gap", 8, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_rd_page_exp_cycles", 16, 8},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_wr_page_exp_cycles", 24, 8}
         });
      this.default_map.add_reg(this.SCHED4, `UVM_REG_ADDR_WIDTH'h390, "RW", 0);
		this.SCHED4_rd_act_idle_gap = this.SCHED4.rd_act_idle_gap;
		this.rd_act_idle_gap = this.SCHED4.rd_act_idle_gap;
		this.SCHED4_wr_act_idle_gap = this.SCHED4.wr_act_idle_gap;
		this.wr_act_idle_gap = this.SCHED4.wr_act_idle_gap;
		this.SCHED4_rd_page_exp_cycles = this.SCHED4.rd_page_exp_cycles;
		this.rd_page_exp_cycles = this.SCHED4.rd_page_exp_cycles;
		this.SCHED4_wr_page_exp_cycles = this.SCHED4.wr_page_exp_cycles;
		this.wr_page_exp_cycles = this.SCHED4.wr_page_exp_cycles;
      this.SCHED5 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SCHED5::type_id::create("SCHED5",,get_full_name());
      if(this.SCHED5.has_coverage(UVM_CVR_REG_BITS))
      	this.SCHED5.cg_bits.option.name = {get_name(), ".", "SCHED5_bits"};
      this.SCHED5.configure(this, null, "");
      this.SCHED5.build();
	  uvm_resource_db#(string)::set({"REG::", SCHED5.get_full_name()}, "accessType", "NONSECURE", this);
         this.SCHED5.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_wrecc_cam_lowthresh", 0, 5},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_wrecc_cam_highthresh", 8, 5},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_dis_opt_loaded_wrecc_cam_fill_level", 28, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_dis_opt_valid_wrecc_cam_fill_level", 29, 1}
         });
      this.default_map.add_reg(this.SCHED5, `UVM_REG_ADDR_WIDTH'h394, "RW", 0);
		this.SCHED5_wrecc_cam_lowthresh = this.SCHED5.wrecc_cam_lowthresh;
		this.wrecc_cam_lowthresh = this.SCHED5.wrecc_cam_lowthresh;
		this.SCHED5_wrecc_cam_highthresh = this.SCHED5.wrecc_cam_highthresh;
		this.wrecc_cam_highthresh = this.SCHED5.wrecc_cam_highthresh;
		this.SCHED5_dis_opt_loaded_wrecc_cam_fill_level = this.SCHED5.dis_opt_loaded_wrecc_cam_fill_level;
		this.dis_opt_loaded_wrecc_cam_fill_level = this.SCHED5.dis_opt_loaded_wrecc_cam_fill_level;
		this.SCHED5_dis_opt_valid_wrecc_cam_fill_level = this.SCHED5.dis_opt_valid_wrecc_cam_fill_level;
		this.dis_opt_valid_wrecc_cam_fill_level = this.SCHED5.dis_opt_valid_wrecc_cam_fill_level;
      this.HWFFCCTL = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_HWFFCCTL::type_id::create("HWFFCCTL",,get_full_name());
      if(this.HWFFCCTL.has_coverage(UVM_CVR_REG_BITS))
      	this.HWFFCCTL.cg_bits.option.name = {get_name(), ".", "HWFFCCTL_bits"};
      this.HWFFCCTL.configure(this, null, "");
      this.HWFFCCTL.build();
	  uvm_resource_db#(string)::set({"REG::", HWFFCCTL.get_full_name()}, "accessType", "NONSECURE", this);
         this.HWFFCCTL.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_hwffc_en", 0, 2},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_init_fsp", 4, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_init_vrcg", 5, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_target_vrcg", 6, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_skip_mrw_odtvref", 24, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_skip_zq_stop_start", 25, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_zq_interval", 26, 2},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_hwffc_mode", 31, 1}
         });
      this.default_map.add_reg(this.HWFFCCTL, `UVM_REG_ADDR_WIDTH'h400, "RW", 0);
		this.HWFFCCTL_hwffc_en = this.HWFFCCTL.hwffc_en;
		this.hwffc_en = this.HWFFCCTL.hwffc_en;
		this.HWFFCCTL_init_fsp = this.HWFFCCTL.init_fsp;
		this.init_fsp = this.HWFFCCTL.init_fsp;
		this.HWFFCCTL_init_vrcg = this.HWFFCCTL.init_vrcg;
		this.init_vrcg = this.HWFFCCTL.init_vrcg;
		this.HWFFCCTL_target_vrcg = this.HWFFCCTL.target_vrcg;
		this.target_vrcg = this.HWFFCCTL.target_vrcg;
		this.HWFFCCTL_skip_mrw_odtvref = this.HWFFCCTL.skip_mrw_odtvref;
		this.skip_mrw_odtvref = this.HWFFCCTL.skip_mrw_odtvref;
		this.HWFFCCTL_skip_zq_stop_start = this.HWFFCCTL.skip_zq_stop_start;
		this.skip_zq_stop_start = this.HWFFCCTL.skip_zq_stop_start;
		this.HWFFCCTL_zq_interval = this.HWFFCCTL.zq_interval;
		this.zq_interval = this.HWFFCCTL.zq_interval;
		this.HWFFCCTL_hwffc_mode = this.HWFFCCTL.hwffc_mode;
		this.hwffc_mode = this.HWFFCCTL.hwffc_mode;
      this.HWFFCSTAT = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_HWFFCSTAT::type_id::create("HWFFCSTAT",,get_full_name());
      if(this.HWFFCSTAT.has_coverage(UVM_CVR_REG_BITS))
      	this.HWFFCSTAT.cg_bits.option.name = {get_name(), ".", "HWFFCSTAT_bits"};
      this.HWFFCSTAT.configure(this, null, "");
      this.HWFFCSTAT.build();
	  uvm_resource_db#(string)::set({"REG::", HWFFCSTAT.get_full_name()}, "accessType", "NONSECURE", this);
         this.HWFFCSTAT.add_hdl_path('{
            '{"ddrc_reg_hwffc_in_progress", 0, 1},
            '{"ddrc_reg_hwffc_operating_mode", 1, 1},
            '{"ddrc_reg_current_frequency", 4, 2},
            '{"ddrc_reg_current_fsp", 8, 1},
            '{"ddrc_reg_current_vrcg", 9, 1}
         });
      this.default_map.add_reg(this.HWFFCSTAT, `UVM_REG_ADDR_WIDTH'h404, "RO", 0);
		this.HWFFCSTAT_hwffc_in_progress = this.HWFFCSTAT.hwffc_in_progress;
		this.hwffc_in_progress = this.HWFFCSTAT.hwffc_in_progress;
		this.HWFFCSTAT_hwffc_operating_mode = this.HWFFCSTAT.hwffc_operating_mode;
		this.hwffc_operating_mode = this.HWFFCSTAT.hwffc_operating_mode;
		this.HWFFCSTAT_current_frequency = this.HWFFCSTAT.current_frequency;
		this.current_frequency = this.HWFFCSTAT.current_frequency;
		this.HWFFCSTAT_current_fsp = this.HWFFCSTAT.current_fsp;
		this.current_fsp = this.HWFFCSTAT.current_fsp;
		this.HWFFCSTAT_current_vrcg = this.HWFFCSTAT.current_vrcg;
		this.current_vrcg = this.HWFFCSTAT.current_vrcg;
      this.DFILPCFG0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFILPCFG0::type_id::create("DFILPCFG0",,get_full_name());
      if(this.DFILPCFG0.has_coverage(UVM_CVR_REG_BITS))
      	this.DFILPCFG0.cg_bits.option.name = {get_name(), ".", "DFILPCFG0_bits"};
      this.DFILPCFG0.configure(this, null, "");
      this.DFILPCFG0.build();
	  uvm_resource_db#(string)::set({"REG::", DFILPCFG0.get_full_name()}, "accessType", "NONSECURE", this);
         this.DFILPCFG0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dfi_lp_en_pd", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dfi_lp_en_sr", 4, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dfi_lp_en_dsm", 8, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dfi_lp_en_data", 16, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dfi_lp_data_req_en", 20, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_extra_gap_for_dfi_lp_data", 28, 2}
         });
      this.default_map.add_reg(this.DFILPCFG0, `UVM_REG_ADDR_WIDTH'h500, "RW", 0);
		this.DFILPCFG0_dfi_lp_en_pd = this.DFILPCFG0.dfi_lp_en_pd;
		this.dfi_lp_en_pd = this.DFILPCFG0.dfi_lp_en_pd;
		this.DFILPCFG0_dfi_lp_en_sr = this.DFILPCFG0.dfi_lp_en_sr;
		this.dfi_lp_en_sr = this.DFILPCFG0.dfi_lp_en_sr;
		this.DFILPCFG0_dfi_lp_en_dsm = this.DFILPCFG0.dfi_lp_en_dsm;
		this.dfi_lp_en_dsm = this.DFILPCFG0.dfi_lp_en_dsm;
		this.DFILPCFG0_dfi_lp_en_data = this.DFILPCFG0.dfi_lp_en_data;
		this.dfi_lp_en_data = this.DFILPCFG0.dfi_lp_en_data;
		this.DFILPCFG0_dfi_lp_data_req_en = this.DFILPCFG0.dfi_lp_data_req_en;
		this.dfi_lp_data_req_en = this.DFILPCFG0.dfi_lp_data_req_en;
		this.DFILPCFG0_extra_gap_for_dfi_lp_data = this.DFILPCFG0.extra_gap_for_dfi_lp_data;
		this.extra_gap_for_dfi_lp_data = this.DFILPCFG0.extra_gap_for_dfi_lp_data;
      this.DFIUPD0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFIUPD0::type_id::create("DFIUPD0",,get_full_name());
      if(this.DFIUPD0.has_coverage(UVM_CVR_REG_BITS))
      	this.DFIUPD0.cg_bits.option.name = {get_name(), ".", "DFIUPD0_bits"};
      this.DFIUPD0.configure(this, null, "");
      this.DFIUPD0.build();
	  uvm_resource_db#(string)::set({"REG::", DFIUPD0.get_full_name()}, "accessType", "NONSECURE", this);
         this.DFIUPD0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dfi_phyupd_en", 15, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ctrlupd_pre_srx", 29, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dis_auto_ctrlupd_srx", 30, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dis_auto_ctrlupd", 31, 1}
         });
      this.default_map.add_reg(this.DFIUPD0, `UVM_REG_ADDR_WIDTH'h508, "RW", 0);
		this.DFIUPD0_dfi_phyupd_en = this.DFIUPD0.dfi_phyupd_en;
		this.dfi_phyupd_en = this.DFIUPD0.dfi_phyupd_en;
		this.DFIUPD0_ctrlupd_pre_srx = this.DFIUPD0.ctrlupd_pre_srx;
		this.ctrlupd_pre_srx = this.DFIUPD0.ctrlupd_pre_srx;
		this.DFIUPD0_dis_auto_ctrlupd_srx = this.DFIUPD0.dis_auto_ctrlupd_srx;
		this.dis_auto_ctrlupd_srx = this.DFIUPD0.dis_auto_ctrlupd_srx;
		this.DFIUPD0_dis_auto_ctrlupd = this.DFIUPD0.dis_auto_ctrlupd;
		this.dis_auto_ctrlupd = this.DFIUPD0.dis_auto_ctrlupd;
      this.DFIMISC = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFIMISC::type_id::create("DFIMISC",,get_full_name());
      if(this.DFIMISC.has_coverage(UVM_CVR_REG_BITS))
      	this.DFIMISC.cg_bits.option.name = {get_name(), ".", "DFIMISC_bits"};
      this.DFIMISC.configure(this, null, "");
      this.DFIMISC.build();
	  uvm_resource_db#(string)::set({"REG::", DFIMISC.get_full_name()}, "accessType", "NONSECURE", this);
         this.DFIMISC.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dfi_init_complete_en", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_phy_dbi_mode", 1, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dfi_data_cs_polarity", 2, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dfi_reset_n", 4, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dfi_init_start", 5, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_lp_optimized_write", 7, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dfi_frequency", 8, 5},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dfi_freq_fsp", 14, 2},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dfi_channel_mode", 16, 2}
         });
      this.default_map.add_reg(this.DFIMISC, `UVM_REG_ADDR_WIDTH'h510, "RW", 0);
		this.DFIMISC_dfi_init_complete_en = this.DFIMISC.dfi_init_complete_en;
		this.dfi_init_complete_en = this.DFIMISC.dfi_init_complete_en;
		this.DFIMISC_phy_dbi_mode = this.DFIMISC.phy_dbi_mode;
		this.phy_dbi_mode = this.DFIMISC.phy_dbi_mode;
		this.DFIMISC_dfi_data_cs_polarity = this.DFIMISC.dfi_data_cs_polarity;
		this.dfi_data_cs_polarity = this.DFIMISC.dfi_data_cs_polarity;
		this.DFIMISC_dfi_reset_n = this.DFIMISC.dfi_reset_n;
		this.dfi_reset_n = this.DFIMISC.dfi_reset_n;
		this.DFIMISC_dfi_init_start = this.DFIMISC.dfi_init_start;
		this.dfi_init_start = this.DFIMISC.dfi_init_start;
		this.DFIMISC_lp_optimized_write = this.DFIMISC.lp_optimized_write;
		this.lp_optimized_write = this.DFIMISC.lp_optimized_write;
		this.DFIMISC_dfi_frequency = this.DFIMISC.dfi_frequency;
		this.dfi_frequency = this.DFIMISC.dfi_frequency;
		this.DFIMISC_dfi_freq_fsp = this.DFIMISC.dfi_freq_fsp;
		this.dfi_freq_fsp = this.DFIMISC.dfi_freq_fsp;
		this.DFIMISC_dfi_channel_mode = this.DFIMISC.dfi_channel_mode;
		this.dfi_channel_mode = this.DFIMISC.dfi_channel_mode;
      this.DFISTAT = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFISTAT::type_id::create("DFISTAT",,get_full_name());
      if(this.DFISTAT.has_coverage(UVM_CVR_REG_BITS))
      	this.DFISTAT.cg_bits.option.name = {get_name(), ".", "DFISTAT_bits"};
      this.DFISTAT.configure(this, null, "");
      this.DFISTAT.build();
	  uvm_resource_db#(string)::set({"REG::", DFISTAT.get_full_name()}, "accessType", "NONSECURE", this);
         this.DFISTAT.add_hdl_path('{
            '{"ddrc_reg_dfi_init_complete", 0, 1},
            '{"ddrc_reg_dfi_lp_ctrl_ack_stat", 1, 1},
            '{"ddrc_reg_dfi_lp_data_ack_stat", 2, 1}
         });
      this.default_map.add_reg(this.DFISTAT, `UVM_REG_ADDR_WIDTH'h514, "RO", 0);
		this.DFISTAT_dfi_init_complete = this.DFISTAT.dfi_init_complete;
		this.dfi_init_complete = this.DFISTAT.dfi_init_complete;
		this.DFISTAT_dfi_lp_ctrl_ack_stat = this.DFISTAT.dfi_lp_ctrl_ack_stat;
		this.dfi_lp_ctrl_ack_stat = this.DFISTAT.dfi_lp_ctrl_ack_stat;
		this.DFISTAT_dfi_lp_data_ack_stat = this.DFISTAT.dfi_lp_data_ack_stat;
		this.dfi_lp_data_ack_stat = this.DFISTAT.dfi_lp_data_ack_stat;
      this.DFIPHYMSTR = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DFIPHYMSTR::type_id::create("DFIPHYMSTR",,get_full_name());
      if(this.DFIPHYMSTR.has_coverage(UVM_CVR_REG_BITS))
      	this.DFIPHYMSTR.cg_bits.option.name = {get_name(), ".", "DFIPHYMSTR_bits"};
      this.DFIPHYMSTR.configure(this, null, "");
      this.DFIPHYMSTR.build();
	  uvm_resource_db#(string)::set({"REG::", DFIPHYMSTR.get_full_name()}, "accessType", "NONSECURE", this);
         this.DFIPHYMSTR.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dfi_phymstr_en", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dfi_phymstr_blk_ref_x32", 24, 8}
         });
      this.default_map.add_reg(this.DFIPHYMSTR, `UVM_REG_ADDR_WIDTH'h518, "RW", 0);
		this.DFIPHYMSTR_dfi_phymstr_en = this.DFIPHYMSTR.dfi_phymstr_en;
		this.dfi_phymstr_en = this.DFIPHYMSTR.dfi_phymstr_en;
		this.DFIPHYMSTR_dfi_phymstr_blk_ref_x32 = this.DFIPHYMSTR.dfi_phymstr_blk_ref_x32;
		this.dfi_phymstr_blk_ref_x32 = this.DFIPHYMSTR.dfi_phymstr_blk_ref_x32;
      this.POISONCFG = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_POISONCFG::type_id::create("POISONCFG",,get_full_name());
      if(this.POISONCFG.has_coverage(UVM_CVR_REG_BITS))
      	this.POISONCFG.cg_bits.option.name = {get_name(), ".", "POISONCFG_bits"};
      this.POISONCFG.configure(this, null, "");
      this.POISONCFG.build();
	  uvm_resource_db#(bit)::set({"REG::", POISONCFG.get_full_name()}, "NO_REG_BIT_BASH_TEST", 1, this);
	  uvm_resource_db#(string)::set({"REG::", POISONCFG.get_full_name()}, "accessType", "NONSECURE", this);
         this.POISONCFG.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_wr_poison_slverr_en", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_wr_poison_intr_en", 4, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_wr_poison_intr_clr", 8, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rd_poison_slverr_en", 16, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rd_poison_intr_en", 20, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rd_poison_intr_clr", 24, 1}
         });
      this.default_map.add_reg(this.POISONCFG, `UVM_REG_ADDR_WIDTH'h580, "RW", 0);
		this.POISONCFG_wr_poison_slverr_en = this.POISONCFG.wr_poison_slverr_en;
		this.wr_poison_slverr_en = this.POISONCFG.wr_poison_slverr_en;
		this.POISONCFG_wr_poison_intr_en = this.POISONCFG.wr_poison_intr_en;
		this.wr_poison_intr_en = this.POISONCFG.wr_poison_intr_en;
		this.POISONCFG_wr_poison_intr_clr = this.POISONCFG.wr_poison_intr_clr;
		this.wr_poison_intr_clr = this.POISONCFG.wr_poison_intr_clr;
		this.POISONCFG_rd_poison_slverr_en = this.POISONCFG.rd_poison_slverr_en;
		this.rd_poison_slverr_en = this.POISONCFG.rd_poison_slverr_en;
		this.POISONCFG_rd_poison_intr_en = this.POISONCFG.rd_poison_intr_en;
		this.rd_poison_intr_en = this.POISONCFG.rd_poison_intr_en;
		this.POISONCFG_rd_poison_intr_clr = this.POISONCFG.rd_poison_intr_clr;
		this.rd_poison_intr_clr = this.POISONCFG.rd_poison_intr_clr;
      this.POISONSTAT = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_POISONSTAT::type_id::create("POISONSTAT",,get_full_name());
      if(this.POISONSTAT.has_coverage(UVM_CVR_REG_BITS))
      	this.POISONSTAT.cg_bits.option.name = {get_name(), ".", "POISONSTAT_bits"};
      this.POISONSTAT.configure(this, null, "");
      this.POISONSTAT.build();
	  uvm_resource_db#(string)::set({"REG::", POISONSTAT.get_full_name()}, "accessType", "NONSECURE", this);
         this.POISONSTAT.add_hdl_path('{
            '{"ddrc_reg_wr_poison_intr_0", 0, 1},
            '{"ddrc_reg_rd_poison_intr_0", 16, 1}
         });
      this.default_map.add_reg(this.POISONSTAT, `UVM_REG_ADDR_WIDTH'h584, "RO", 0);
		this.POISONSTAT_wr_poison_intr_0 = this.POISONSTAT.wr_poison_intr_0;
		this.wr_poison_intr_0 = this.POISONSTAT.wr_poison_intr_0;
		this.POISONSTAT_rd_poison_intr_0 = this.POISONSTAT.rd_poison_intr_0;
		this.rd_poison_intr_0 = this.POISONSTAT.rd_poison_intr_0;
      this.ECCCFG0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCFG0::type_id::create("ECCCFG0",,get_full_name());
      if(this.ECCCFG0.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCCFG0.cg_bits.option.name = {get_name(), ".", "ECCCFG0_bits"};
      this.ECCCFG0.configure(this, null, "");
      this.ECCCFG0.build();
	  uvm_resource_db#(string)::set({"REG::", ECCCFG0.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCCFG0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ecc_mode", 0, 3},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ecc_ap_en", 6, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ecc_region_remap_en", 7, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ecc_region_map", 8, 7},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_blk_channel_idle_time_x32", 16, 6},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ecc_ap_err_threshold", 24, 3},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ecc_region_map_other", 29, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ecc_region_map_granu", 30, 2}
         });
      this.default_map.add_reg(this.ECCCFG0, `UVM_REG_ADDR_WIDTH'h600, "RW", 0);
		this.ECCCFG0_ecc_mode = this.ECCCFG0.ecc_mode;
		this.ecc_mode = this.ECCCFG0.ecc_mode;
		this.ECCCFG0_ecc_ap_en = this.ECCCFG0.ecc_ap_en;
		this.ecc_ap_en = this.ECCCFG0.ecc_ap_en;
		this.ECCCFG0_ecc_region_remap_en = this.ECCCFG0.ecc_region_remap_en;
		this.ecc_region_remap_en = this.ECCCFG0.ecc_region_remap_en;
		this.ECCCFG0_ecc_region_map = this.ECCCFG0.ecc_region_map;
		this.ecc_region_map = this.ECCCFG0.ecc_region_map;
		this.ECCCFG0_blk_channel_idle_time_x32 = this.ECCCFG0.blk_channel_idle_time_x32;
		this.blk_channel_idle_time_x32 = this.ECCCFG0.blk_channel_idle_time_x32;
		this.ECCCFG0_ecc_ap_err_threshold = this.ECCCFG0.ecc_ap_err_threshold;
		this.ecc_ap_err_threshold = this.ECCCFG0.ecc_ap_err_threshold;
		this.ECCCFG0_ecc_region_map_other = this.ECCCFG0.ecc_region_map_other;
		this.ecc_region_map_other = this.ECCCFG0.ecc_region_map_other;
		this.ECCCFG0_ecc_region_map_granu = this.ECCCFG0.ecc_region_map_granu;
		this.ecc_region_map_granu = this.ECCCFG0.ecc_region_map_granu;
      this.ECCCFG1 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCFG1::type_id::create("ECCCFG1",,get_full_name());
      if(this.ECCCFG1.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCCFG1.cg_bits.option.name = {get_name(), ".", "ECCCFG1_bits"};
      this.ECCCFG1.configure(this, null, "");
      this.ECCCFG1.build();
	  uvm_resource_db#(string)::set({"REG::", ECCCFG1.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCCFG1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_data_poison_en", 0, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_data_poison_bit", 1, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_ecc_region_parity_lock", 4, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_ecc_region_waste_lock", 5, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_med_ecc_en", 6, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_blk_channel_active_term", 7, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_active_blk_channel", 8, 5}
         });
      this.default_map.add_reg(this.ECCCFG1, `UVM_REG_ADDR_WIDTH'h604, "RW", 0);
		this.ECCCFG1_data_poison_en = this.ECCCFG1.data_poison_en;
		this.data_poison_en = this.ECCCFG1.data_poison_en;
		this.ECCCFG1_data_poison_bit = this.ECCCFG1.data_poison_bit;
		this.data_poison_bit = this.ECCCFG1.data_poison_bit;
		this.ECCCFG1_ecc_region_parity_lock = this.ECCCFG1.ecc_region_parity_lock;
		this.ecc_region_parity_lock = this.ECCCFG1.ecc_region_parity_lock;
		this.ECCCFG1_ecc_region_waste_lock = this.ECCCFG1.ecc_region_waste_lock;
		this.ecc_region_waste_lock = this.ECCCFG1.ecc_region_waste_lock;
		this.ECCCFG1_med_ecc_en = this.ECCCFG1.med_ecc_en;
		this.med_ecc_en = this.ECCCFG1.med_ecc_en;
		this.ECCCFG1_blk_channel_active_term = this.ECCCFG1.blk_channel_active_term;
		this.blk_channel_active_term = this.ECCCFG1.blk_channel_active_term;
		this.ECCCFG1_active_blk_channel = this.ECCCFG1.active_blk_channel;
		this.active_blk_channel = this.ECCCFG1.active_blk_channel;
      this.ECCSTAT = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCSTAT::type_id::create("ECCSTAT",,get_full_name());
      if(this.ECCSTAT.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCSTAT.cg_bits.option.name = {get_name(), ".", "ECCSTAT_bits"};
      this.ECCSTAT.configure(this, null, "");
      this.ECCSTAT.build();
	  uvm_resource_db#(string)::set({"REG::", ECCSTAT.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCSTAT.add_hdl_path('{
            '{"ddrc_reg_ecc_corrected_bit_num", 0, 7},
            '{"ddrc_reg_ecc_corrected_err", 8, 1},
            '{"ddrc_reg_ecc_uncorrected_err", 16, 1},
            '{"ddrc_reg_sbr_read_ecc_ce", 24, 1},
            '{"ddrc_reg_sbr_read_ecc_ue", 25, 1}
         });
      this.default_map.add_reg(this.ECCSTAT, `UVM_REG_ADDR_WIDTH'h608, "RO", 0);
		this.ECCSTAT_ecc_corrected_bit_num = this.ECCSTAT.ecc_corrected_bit_num;
		this.ecc_corrected_bit_num = this.ECCSTAT.ecc_corrected_bit_num;
		this.ECCSTAT_ecc_corrected_err = this.ECCSTAT.ecc_corrected_err;
		this.ecc_corrected_err = this.ECCSTAT.ecc_corrected_err;
		this.ECCSTAT_ecc_uncorrected_err = this.ECCSTAT.ecc_uncorrected_err;
		this.ecc_uncorrected_err = this.ECCSTAT.ecc_uncorrected_err;
		this.ECCSTAT_sbr_read_ecc_ce = this.ECCSTAT.sbr_read_ecc_ce;
		this.sbr_read_ecc_ce = this.ECCSTAT.sbr_read_ecc_ce;
		this.ECCSTAT_sbr_read_ecc_ue = this.ECCSTAT.sbr_read_ecc_ue;
		this.sbr_read_ecc_ue = this.ECCSTAT.sbr_read_ecc_ue;
      this.ECCCTL = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCTL::type_id::create("ECCCTL",,get_full_name());
      if(this.ECCCTL.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCCTL.cg_bits.option.name = {get_name(), ".", "ECCCTL_bits"};
      this.ECCCTL.configure(this, null, "");
      this.ECCCTL.build();
	  uvm_resource_db#(bit)::set({"REG::", ECCCTL.get_full_name()}, "NO_REG_BIT_BASH_TEST", 1, this);
	  uvm_resource_db#(string)::set({"REG::", ECCCTL.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCCTL.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ecc_corrected_err_clr", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ecc_uncorrected_err_clr", 1, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ecc_corr_err_cnt_clr", 2, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ecc_uncorr_err_cnt_clr", 3, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ecc_ap_err_intr_clr", 4, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ecc_corrected_err_intr_en", 8, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ecc_uncorrected_err_intr_en", 9, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ecc_ap_err_intr_en", 10, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ecc_corrected_err_intr_force", 16, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ecc_uncorrected_err_intr_force", 17, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ecc_ap_err_intr_force", 18, 1}
         });
      this.default_map.add_reg(this.ECCCTL, `UVM_REG_ADDR_WIDTH'h60C, "RW", 0);
		this.ECCCTL_ecc_corrected_err_clr = this.ECCCTL.ecc_corrected_err_clr;
		this.ecc_corrected_err_clr = this.ECCCTL.ecc_corrected_err_clr;
		this.ECCCTL_ecc_uncorrected_err_clr = this.ECCCTL.ecc_uncorrected_err_clr;
		this.ecc_uncorrected_err_clr = this.ECCCTL.ecc_uncorrected_err_clr;
		this.ECCCTL_ecc_corr_err_cnt_clr = this.ECCCTL.ecc_corr_err_cnt_clr;
		this.ecc_corr_err_cnt_clr = this.ECCCTL.ecc_corr_err_cnt_clr;
		this.ECCCTL_ecc_uncorr_err_cnt_clr = this.ECCCTL.ecc_uncorr_err_cnt_clr;
		this.ecc_uncorr_err_cnt_clr = this.ECCCTL.ecc_uncorr_err_cnt_clr;
		this.ECCCTL_ecc_ap_err_intr_clr = this.ECCCTL.ecc_ap_err_intr_clr;
		this.ecc_ap_err_intr_clr = this.ECCCTL.ecc_ap_err_intr_clr;
		this.ECCCTL_ecc_corrected_err_intr_en = this.ECCCTL.ecc_corrected_err_intr_en;
		this.ecc_corrected_err_intr_en = this.ECCCTL.ecc_corrected_err_intr_en;
		this.ECCCTL_ecc_uncorrected_err_intr_en = this.ECCCTL.ecc_uncorrected_err_intr_en;
		this.ecc_uncorrected_err_intr_en = this.ECCCTL.ecc_uncorrected_err_intr_en;
		this.ECCCTL_ecc_ap_err_intr_en = this.ECCCTL.ecc_ap_err_intr_en;
		this.ecc_ap_err_intr_en = this.ECCCTL.ecc_ap_err_intr_en;
		this.ECCCTL_ecc_corrected_err_intr_force = this.ECCCTL.ecc_corrected_err_intr_force;
		this.ecc_corrected_err_intr_force = this.ECCCTL.ecc_corrected_err_intr_force;
		this.ECCCTL_ecc_uncorrected_err_intr_force = this.ECCCTL.ecc_uncorrected_err_intr_force;
		this.ecc_uncorrected_err_intr_force = this.ECCCTL.ecc_uncorrected_err_intr_force;
		this.ECCCTL_ecc_ap_err_intr_force = this.ECCCTL.ecc_ap_err_intr_force;
		this.ecc_ap_err_intr_force = this.ECCCTL.ecc_ap_err_intr_force;
      this.ECCERRCNT = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCERRCNT::type_id::create("ECCERRCNT",,get_full_name());
      if(this.ECCERRCNT.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCERRCNT.cg_bits.option.name = {get_name(), ".", "ECCERRCNT_bits"};
      this.ECCERRCNT.configure(this, null, "");
      this.ECCERRCNT.build();
	  uvm_resource_db#(string)::set({"REG::", ECCERRCNT.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCERRCNT.add_hdl_path('{
            '{"ddrc_reg_ecc_corr_err_cnt", 0, 16},
            '{"ddrc_reg_ecc_uncorr_err_cnt", 16, 16}
         });
      this.default_map.add_reg(this.ECCERRCNT, `UVM_REG_ADDR_WIDTH'h610, "RO", 0);
		this.ECCERRCNT_ecc_corr_err_cnt = this.ECCERRCNT.ecc_corr_err_cnt;
		this.ecc_corr_err_cnt = this.ECCERRCNT.ecc_corr_err_cnt;
		this.ECCERRCNT_ecc_uncorr_err_cnt = this.ECCERRCNT.ecc_uncorr_err_cnt;
		this.ecc_uncorr_err_cnt = this.ECCERRCNT.ecc_uncorr_err_cnt;
      this.ECCCADDR0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCADDR0::type_id::create("ECCCADDR0",,get_full_name());
      if(this.ECCCADDR0.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCCADDR0.cg_bits.option.name = {get_name(), ".", "ECCCADDR0_bits"};
      this.ECCCADDR0.configure(this, null, "");
      this.ECCCADDR0.build();
	  uvm_resource_db#(string)::set({"REG::", ECCCADDR0.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCCADDR0.add_hdl_path('{
            '{"ddrc_reg_ecc_corr_row", 0, 18},
            '{"ddrc_reg_ecc_corr_rank", 24, 1}
         });
      this.default_map.add_reg(this.ECCCADDR0, `UVM_REG_ADDR_WIDTH'h614, "RO", 0);
		this.ECCCADDR0_ecc_corr_row = this.ECCCADDR0.ecc_corr_row;
		this.ecc_corr_row = this.ECCCADDR0.ecc_corr_row;
		this.ECCCADDR0_ecc_corr_rank = this.ECCCADDR0.ecc_corr_rank;
		this.ecc_corr_rank = this.ECCCADDR0.ecc_corr_rank;
      this.ECCCADDR1 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCADDR1::type_id::create("ECCCADDR1",,get_full_name());
      if(this.ECCCADDR1.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCCADDR1.cg_bits.option.name = {get_name(), ".", "ECCCADDR1_bits"};
      this.ECCCADDR1.configure(this, null, "");
      this.ECCCADDR1.build();
	  uvm_resource_db#(string)::set({"REG::", ECCCADDR1.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCCADDR1.add_hdl_path('{
            '{"ddrc_reg_ecc_corr_col", 0, 11},
            '{"ddrc_reg_ecc_corr_bank", 16, 3},
            '{"ddrc_reg_ecc_corr_bg", 24, 2}
         });
      this.default_map.add_reg(this.ECCCADDR1, `UVM_REG_ADDR_WIDTH'h618, "RO", 0);
		this.ECCCADDR1_ecc_corr_col = this.ECCCADDR1.ecc_corr_col;
		this.ecc_corr_col = this.ECCCADDR1.ecc_corr_col;
		this.ECCCADDR1_ecc_corr_bank = this.ECCCADDR1.ecc_corr_bank;
		this.ecc_corr_bank = this.ECCCADDR1.ecc_corr_bank;
		this.ECCCADDR1_ecc_corr_bg = this.ECCCADDR1.ecc_corr_bg;
		this.ecc_corr_bg = this.ECCCADDR1.ecc_corr_bg;
      this.ECCCSYN0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCSYN0::type_id::create("ECCCSYN0",,get_full_name());
      if(this.ECCCSYN0.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCCSYN0.cg_bits.option.name = {get_name(), ".", "ECCCSYN0_bits"};
      this.ECCCSYN0.configure(this, null, "");
      this.ECCCSYN0.build();
	  uvm_resource_db#(string)::set({"REG::", ECCCSYN0.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCCSYN0.add_hdl_path('{
            '{"ddrc_reg_ecc_corr_syndromes_31_0", 0, 32}
         });
      this.default_map.add_reg(this.ECCCSYN0, `UVM_REG_ADDR_WIDTH'h61C, "RO", 0);
		this.ECCCSYN0_ecc_corr_syndromes_31_0 = this.ECCCSYN0.ecc_corr_syndromes_31_0;
		this.ecc_corr_syndromes_31_0 = this.ECCCSYN0.ecc_corr_syndromes_31_0;
      this.ECCCSYN1 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCSYN1::type_id::create("ECCCSYN1",,get_full_name());
      if(this.ECCCSYN1.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCCSYN1.cg_bits.option.name = {get_name(), ".", "ECCCSYN1_bits"};
      this.ECCCSYN1.configure(this, null, "");
      this.ECCCSYN1.build();
	  uvm_resource_db#(string)::set({"REG::", ECCCSYN1.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCCSYN1.add_hdl_path('{
            '{"ddrc_reg_ecc_corr_syndromes_63_32", 0, 32}
         });
      this.default_map.add_reg(this.ECCCSYN1, `UVM_REG_ADDR_WIDTH'h620, "RO", 0);
		this.ECCCSYN1_ecc_corr_syndromes_63_32 = this.ECCCSYN1.ecc_corr_syndromes_63_32;
		this.ecc_corr_syndromes_63_32 = this.ECCCSYN1.ecc_corr_syndromes_63_32;
      this.ECCCSYN2 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCCSYN2::type_id::create("ECCCSYN2",,get_full_name());
      if(this.ECCCSYN2.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCCSYN2.cg_bits.option.name = {get_name(), ".", "ECCCSYN2_bits"};
      this.ECCCSYN2.configure(this, null, "");
      this.ECCCSYN2.build();
	  uvm_resource_db#(string)::set({"REG::", ECCCSYN2.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCCSYN2.add_hdl_path('{
            '{"ddrc_reg_ecc_corr_syndromes_71_64", 0, 8}
         });
      this.default_map.add_reg(this.ECCCSYN2, `UVM_REG_ADDR_WIDTH'h624, "RO", 0);
		this.ECCCSYN2_ecc_corr_syndromes_71_64 = this.ECCCSYN2.ecc_corr_syndromes_71_64;
		this.ecc_corr_syndromes_71_64 = this.ECCCSYN2.ecc_corr_syndromes_71_64;
      this.ECCBITMASK0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCBITMASK0::type_id::create("ECCBITMASK0",,get_full_name());
      if(this.ECCBITMASK0.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCBITMASK0.cg_bits.option.name = {get_name(), ".", "ECCBITMASK0_bits"};
      this.ECCBITMASK0.configure(this, null, "");
      this.ECCBITMASK0.build();
	  uvm_resource_db#(string)::set({"REG::", ECCBITMASK0.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCBITMASK0.add_hdl_path('{
            '{"ddrc_reg_ecc_corr_bit_mask_31_0", 0, 32}
         });
      this.default_map.add_reg(this.ECCBITMASK0, `UVM_REG_ADDR_WIDTH'h628, "RO", 0);
		this.ECCBITMASK0_ecc_corr_bit_mask_31_0 = this.ECCBITMASK0.ecc_corr_bit_mask_31_0;
		this.ecc_corr_bit_mask_31_0 = this.ECCBITMASK0.ecc_corr_bit_mask_31_0;
      this.ECCBITMASK1 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCBITMASK1::type_id::create("ECCBITMASK1",,get_full_name());
      if(this.ECCBITMASK1.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCBITMASK1.cg_bits.option.name = {get_name(), ".", "ECCBITMASK1_bits"};
      this.ECCBITMASK1.configure(this, null, "");
      this.ECCBITMASK1.build();
	  uvm_resource_db#(string)::set({"REG::", ECCBITMASK1.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCBITMASK1.add_hdl_path('{
            '{"ddrc_reg_ecc_corr_bit_mask_63_32", 0, 32}
         });
      this.default_map.add_reg(this.ECCBITMASK1, `UVM_REG_ADDR_WIDTH'h62C, "RO", 0);
		this.ECCBITMASK1_ecc_corr_bit_mask_63_32 = this.ECCBITMASK1.ecc_corr_bit_mask_63_32;
		this.ecc_corr_bit_mask_63_32 = this.ECCBITMASK1.ecc_corr_bit_mask_63_32;
      this.ECCBITMASK2 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCBITMASK2::type_id::create("ECCBITMASK2",,get_full_name());
      if(this.ECCBITMASK2.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCBITMASK2.cg_bits.option.name = {get_name(), ".", "ECCBITMASK2_bits"};
      this.ECCBITMASK2.configure(this, null, "");
      this.ECCBITMASK2.build();
	  uvm_resource_db#(string)::set({"REG::", ECCBITMASK2.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCBITMASK2.add_hdl_path('{
            '{"ddrc_reg_ecc_corr_bit_mask_71_64", 0, 8}
         });
      this.default_map.add_reg(this.ECCBITMASK2, `UVM_REG_ADDR_WIDTH'h630, "RO", 0);
		this.ECCBITMASK2_ecc_corr_bit_mask_71_64 = this.ECCBITMASK2.ecc_corr_bit_mask_71_64;
		this.ecc_corr_bit_mask_71_64 = this.ECCBITMASK2.ecc_corr_bit_mask_71_64;
      this.ECCUADDR0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUADDR0::type_id::create("ECCUADDR0",,get_full_name());
      if(this.ECCUADDR0.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCUADDR0.cg_bits.option.name = {get_name(), ".", "ECCUADDR0_bits"};
      this.ECCUADDR0.configure(this, null, "");
      this.ECCUADDR0.build();
	  uvm_resource_db#(string)::set({"REG::", ECCUADDR0.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCUADDR0.add_hdl_path('{
            '{"ddrc_reg_ecc_uncorr_row", 0, 18},
            '{"ddrc_reg_ecc_uncorr_rank", 24, 1}
         });
      this.default_map.add_reg(this.ECCUADDR0, `UVM_REG_ADDR_WIDTH'h634, "RO", 0);
		this.ECCUADDR0_ecc_uncorr_row = this.ECCUADDR0.ecc_uncorr_row;
		this.ecc_uncorr_row = this.ECCUADDR0.ecc_uncorr_row;
		this.ECCUADDR0_ecc_uncorr_rank = this.ECCUADDR0.ecc_uncorr_rank;
		this.ecc_uncorr_rank = this.ECCUADDR0.ecc_uncorr_rank;
      this.ECCUADDR1 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUADDR1::type_id::create("ECCUADDR1",,get_full_name());
      if(this.ECCUADDR1.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCUADDR1.cg_bits.option.name = {get_name(), ".", "ECCUADDR1_bits"};
      this.ECCUADDR1.configure(this, null, "");
      this.ECCUADDR1.build();
	  uvm_resource_db#(string)::set({"REG::", ECCUADDR1.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCUADDR1.add_hdl_path('{
            '{"ddrc_reg_ecc_uncorr_col", 0, 11},
            '{"ddrc_reg_ecc_uncorr_bank", 16, 3},
            '{"ddrc_reg_ecc_uncorr_bg", 24, 2}
         });
      this.default_map.add_reg(this.ECCUADDR1, `UVM_REG_ADDR_WIDTH'h638, "RO", 0);
		this.ECCUADDR1_ecc_uncorr_col = this.ECCUADDR1.ecc_uncorr_col;
		this.ecc_uncorr_col = this.ECCUADDR1.ecc_uncorr_col;
		this.ECCUADDR1_ecc_uncorr_bank = this.ECCUADDR1.ecc_uncorr_bank;
		this.ecc_uncorr_bank = this.ECCUADDR1.ecc_uncorr_bank;
		this.ECCUADDR1_ecc_uncorr_bg = this.ECCUADDR1.ecc_uncorr_bg;
		this.ecc_uncorr_bg = this.ECCUADDR1.ecc_uncorr_bg;
      this.ECCUSYN0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUSYN0::type_id::create("ECCUSYN0",,get_full_name());
      if(this.ECCUSYN0.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCUSYN0.cg_bits.option.name = {get_name(), ".", "ECCUSYN0_bits"};
      this.ECCUSYN0.configure(this, null, "");
      this.ECCUSYN0.build();
	  uvm_resource_db#(string)::set({"REG::", ECCUSYN0.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCUSYN0.add_hdl_path('{
            '{"ddrc_reg_ecc_uncorr_syndromes_31_0", 0, 32}
         });
      this.default_map.add_reg(this.ECCUSYN0, `UVM_REG_ADDR_WIDTH'h63C, "RO", 0);
		this.ECCUSYN0_ecc_uncorr_syndromes_31_0 = this.ECCUSYN0.ecc_uncorr_syndromes_31_0;
		this.ecc_uncorr_syndromes_31_0 = this.ECCUSYN0.ecc_uncorr_syndromes_31_0;
      this.ECCUSYN1 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUSYN1::type_id::create("ECCUSYN1",,get_full_name());
      if(this.ECCUSYN1.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCUSYN1.cg_bits.option.name = {get_name(), ".", "ECCUSYN1_bits"};
      this.ECCUSYN1.configure(this, null, "");
      this.ECCUSYN1.build();
	  uvm_resource_db#(string)::set({"REG::", ECCUSYN1.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCUSYN1.add_hdl_path('{
            '{"ddrc_reg_ecc_uncorr_syndromes_63_32", 0, 32}
         });
      this.default_map.add_reg(this.ECCUSYN1, `UVM_REG_ADDR_WIDTH'h640, "RO", 0);
		this.ECCUSYN1_ecc_uncorr_syndromes_63_32 = this.ECCUSYN1.ecc_uncorr_syndromes_63_32;
		this.ecc_uncorr_syndromes_63_32 = this.ECCUSYN1.ecc_uncorr_syndromes_63_32;
      this.ECCUSYN2 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCUSYN2::type_id::create("ECCUSYN2",,get_full_name());
      if(this.ECCUSYN2.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCUSYN2.cg_bits.option.name = {get_name(), ".", "ECCUSYN2_bits"};
      this.ECCUSYN2.configure(this, null, "");
      this.ECCUSYN2.build();
	  uvm_resource_db#(string)::set({"REG::", ECCUSYN2.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCUSYN2.add_hdl_path('{
            '{"ddrc_reg_ecc_uncorr_syndromes_71_64", 0, 8}
         });
      this.default_map.add_reg(this.ECCUSYN2, `UVM_REG_ADDR_WIDTH'h644, "RO", 0);
		this.ECCUSYN2_ecc_uncorr_syndromes_71_64 = this.ECCUSYN2.ecc_uncorr_syndromes_71_64;
		this.ecc_uncorr_syndromes_71_64 = this.ECCUSYN2.ecc_uncorr_syndromes_71_64;
      this.ECCPOISONADDR0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONADDR0::type_id::create("ECCPOISONADDR0",,get_full_name());
      if(this.ECCPOISONADDR0.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCPOISONADDR0.cg_bits.option.name = {get_name(), ".", "ECCPOISONADDR0_bits"};
      this.ECCPOISONADDR0.configure(this, null, "");
      this.ECCPOISONADDR0.build();
	  uvm_resource_db#(string)::set({"REG::", ECCPOISONADDR0.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCPOISONADDR0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_ecc_poison_col", 0, 12},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_ecc_poison_rank", 24, 1}
         });
      this.default_map.add_reg(this.ECCPOISONADDR0, `UVM_REG_ADDR_WIDTH'h648, "RW", 0);
		this.ECCPOISONADDR0_ecc_poison_col = this.ECCPOISONADDR0.ecc_poison_col;
		this.ecc_poison_col = this.ECCPOISONADDR0.ecc_poison_col;
		this.ECCPOISONADDR0_ecc_poison_rank = this.ECCPOISONADDR0.ecc_poison_rank;
		this.ecc_poison_rank = this.ECCPOISONADDR0.ecc_poison_rank;
      this.ECCPOISONADDR1 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONADDR1::type_id::create("ECCPOISONADDR1",,get_full_name());
      if(this.ECCPOISONADDR1.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCPOISONADDR1.cg_bits.option.name = {get_name(), ".", "ECCPOISONADDR1_bits"};
      this.ECCPOISONADDR1.configure(this, null, "");
      this.ECCPOISONADDR1.build();
	  uvm_resource_db#(string)::set({"REG::", ECCPOISONADDR1.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCPOISONADDR1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_ecc_poison_row", 0, 18},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_ecc_poison_bank", 24, 3},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_ecc_poison_bg", 28, 2}
         });
      this.default_map.add_reg(this.ECCPOISONADDR1, `UVM_REG_ADDR_WIDTH'h64C, "RW", 0);
		this.ECCPOISONADDR1_ecc_poison_row = this.ECCPOISONADDR1.ecc_poison_row;
		this.ecc_poison_row = this.ECCPOISONADDR1.ecc_poison_row;
		this.ECCPOISONADDR1_ecc_poison_bank = this.ECCPOISONADDR1.ecc_poison_bank;
		this.ecc_poison_bank = this.ECCPOISONADDR1.ecc_poison_bank;
		this.ECCPOISONADDR1_ecc_poison_bg = this.ECCPOISONADDR1.ecc_poison_bg;
		this.ecc_poison_bg = this.ECCPOISONADDR1.ecc_poison_bg;
      this.ECCPOISONPAT0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONPAT0::type_id::create("ECCPOISONPAT0",,get_full_name());
      if(this.ECCPOISONPAT0.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCPOISONPAT0.cg_bits.option.name = {get_name(), ".", "ECCPOISONPAT0_bits"};
      this.ECCPOISONPAT0.configure(this, null, "");
      this.ECCPOISONPAT0.build();
	  uvm_resource_db#(string)::set({"REG::", ECCPOISONPAT0.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCPOISONPAT0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_ecc_poison_data_31_0", 0, 32}
         });
      this.default_map.add_reg(this.ECCPOISONPAT0, `UVM_REG_ADDR_WIDTH'h658, "RW", 0);
		this.ECCPOISONPAT0_ecc_poison_data_31_0 = this.ECCPOISONPAT0.ecc_poison_data_31_0;
		this.ecc_poison_data_31_0 = this.ECCPOISONPAT0.ecc_poison_data_31_0;
      this.ECCPOISONPAT2 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCPOISONPAT2::type_id::create("ECCPOISONPAT2",,get_full_name());
      if(this.ECCPOISONPAT2.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCPOISONPAT2.cg_bits.option.name = {get_name(), ".", "ECCPOISONPAT2_bits"};
      this.ECCPOISONPAT2.configure(this, null, "");
      this.ECCPOISONPAT2.build();
	  uvm_resource_db#(string)::set({"REG::", ECCPOISONPAT2.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCPOISONPAT2.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_ecc_poison_data_71_64", 0, 8}
         });
      this.default_map.add_reg(this.ECCPOISONPAT2, `UVM_REG_ADDR_WIDTH'h660, "RW", 0);
		this.ECCPOISONPAT2_ecc_poison_data_71_64 = this.ECCPOISONPAT2.ecc_poison_data_71_64;
		this.ecc_poison_data_71_64 = this.ECCPOISONPAT2.ecc_poison_data_71_64;
      this.ECCAPSTAT = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ECCAPSTAT::type_id::create("ECCAPSTAT",,get_full_name());
      if(this.ECCAPSTAT.has_coverage(UVM_CVR_REG_BITS))
      	this.ECCAPSTAT.cg_bits.option.name = {get_name(), ".", "ECCAPSTAT_bits"};
      this.ECCAPSTAT.configure(this, null, "");
      this.ECCAPSTAT.build();
	  uvm_resource_db#(string)::set({"REG::", ECCAPSTAT.get_full_name()}, "accessType", "NONSECURE", this);
         this.ECCAPSTAT.add_hdl_path('{
            '{"ddrc_reg_ecc_ap_err", 0, 1}
         });
      this.default_map.add_reg(this.ECCAPSTAT, `UVM_REG_ADDR_WIDTH'h664, "RO", 0);
		this.ECCAPSTAT_ecc_ap_err = this.ECCAPSTAT.ecc_ap_err;
		this.ecc_ap_err = this.ECCAPSTAT.ecc_ap_err;
      this.LNKECCCTL1 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCCTL1::type_id::create("LNKECCCTL1",,get_full_name());
      if(this.LNKECCCTL1.has_coverage(UVM_CVR_REG_BITS))
      	this.LNKECCCTL1.cg_bits.option.name = {get_name(), ".", "LNKECCCTL1_bits"};
      this.LNKECCCTL1.configure(this, null, "");
      this.LNKECCCTL1.build();
	  uvm_resource_db#(bit)::set({"REG::", LNKECCCTL1.get_full_name()}, "NO_REG_BIT_BASH_TEST", 1, this);
	  uvm_resource_db#(string)::set({"REG::", LNKECCCTL1.get_full_name()}, "accessType", "NONSECURE", this);
         this.LNKECCCTL1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rd_link_ecc_corr_intr_en", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rd_link_ecc_corr_intr_clr", 1, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rd_link_ecc_corr_cnt_clr", 2, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rd_link_ecc_corr_intr_force", 3, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rd_link_ecc_uncorr_intr_en", 4, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rd_link_ecc_uncorr_intr_clr", 5, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rd_link_ecc_uncorr_cnt_clr", 6, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rd_link_ecc_uncorr_intr_force", 7, 1}
         });
      this.default_map.add_reg(this.LNKECCCTL1, `UVM_REG_ADDR_WIDTH'h984, "RW", 0);
		this.LNKECCCTL1_rd_link_ecc_corr_intr_en = this.LNKECCCTL1.rd_link_ecc_corr_intr_en;
		this.rd_link_ecc_corr_intr_en = this.LNKECCCTL1.rd_link_ecc_corr_intr_en;
		this.LNKECCCTL1_rd_link_ecc_corr_intr_clr = this.LNKECCCTL1.rd_link_ecc_corr_intr_clr;
		this.rd_link_ecc_corr_intr_clr = this.LNKECCCTL1.rd_link_ecc_corr_intr_clr;
		this.LNKECCCTL1_rd_link_ecc_corr_cnt_clr = this.LNKECCCTL1.rd_link_ecc_corr_cnt_clr;
		this.rd_link_ecc_corr_cnt_clr = this.LNKECCCTL1.rd_link_ecc_corr_cnt_clr;
		this.LNKECCCTL1_rd_link_ecc_corr_intr_force = this.LNKECCCTL1.rd_link_ecc_corr_intr_force;
		this.rd_link_ecc_corr_intr_force = this.LNKECCCTL1.rd_link_ecc_corr_intr_force;
		this.LNKECCCTL1_rd_link_ecc_uncorr_intr_en = this.LNKECCCTL1.rd_link_ecc_uncorr_intr_en;
		this.rd_link_ecc_uncorr_intr_en = this.LNKECCCTL1.rd_link_ecc_uncorr_intr_en;
		this.LNKECCCTL1_rd_link_ecc_uncorr_intr_clr = this.LNKECCCTL1.rd_link_ecc_uncorr_intr_clr;
		this.rd_link_ecc_uncorr_intr_clr = this.LNKECCCTL1.rd_link_ecc_uncorr_intr_clr;
		this.LNKECCCTL1_rd_link_ecc_uncorr_cnt_clr = this.LNKECCCTL1.rd_link_ecc_uncorr_cnt_clr;
		this.rd_link_ecc_uncorr_cnt_clr = this.LNKECCCTL1.rd_link_ecc_uncorr_cnt_clr;
		this.LNKECCCTL1_rd_link_ecc_uncorr_intr_force = this.LNKECCCTL1.rd_link_ecc_uncorr_intr_force;
		this.rd_link_ecc_uncorr_intr_force = this.LNKECCCTL1.rd_link_ecc_uncorr_intr_force;
      this.LNKECCPOISONCTL0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCPOISONCTL0::type_id::create("LNKECCPOISONCTL0",,get_full_name());
      if(this.LNKECCPOISONCTL0.has_coverage(UVM_CVR_REG_BITS))
      	this.LNKECCPOISONCTL0.cg_bits.option.name = {get_name(), ".", "LNKECCPOISONCTL0_bits"};
      this.LNKECCPOISONCTL0.configure(this, null, "");
      this.LNKECCPOISONCTL0.build();
	  uvm_resource_db#(string)::set({"REG::", LNKECCPOISONCTL0.get_full_name()}, "accessType", "NONSECURE", this);
         this.LNKECCPOISONCTL0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_linkecc_poison_inject_en", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_linkecc_poison_type", 1, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_linkecc_poison_rw", 2, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_linkecc_poison_dmi_sel", 16, 4},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_linkecc_poison_byte_sel", 24, 4}
         });
      this.default_map.add_reg(this.LNKECCPOISONCTL0, `UVM_REG_ADDR_WIDTH'h988, "RW", 0);
		this.LNKECCPOISONCTL0_linkecc_poison_inject_en = this.LNKECCPOISONCTL0.linkecc_poison_inject_en;
		this.linkecc_poison_inject_en = this.LNKECCPOISONCTL0.linkecc_poison_inject_en;
		this.LNKECCPOISONCTL0_linkecc_poison_type = this.LNKECCPOISONCTL0.linkecc_poison_type;
		this.linkecc_poison_type = this.LNKECCPOISONCTL0.linkecc_poison_type;
		this.LNKECCPOISONCTL0_linkecc_poison_rw = this.LNKECCPOISONCTL0.linkecc_poison_rw;
		this.linkecc_poison_rw = this.LNKECCPOISONCTL0.linkecc_poison_rw;
		this.LNKECCPOISONCTL0_linkecc_poison_dmi_sel = this.LNKECCPOISONCTL0.linkecc_poison_dmi_sel;
		this.linkecc_poison_dmi_sel = this.LNKECCPOISONCTL0.linkecc_poison_dmi_sel;
		this.LNKECCPOISONCTL0_linkecc_poison_byte_sel = this.LNKECCPOISONCTL0.linkecc_poison_byte_sel;
		this.linkecc_poison_byte_sel = this.LNKECCPOISONCTL0.linkecc_poison_byte_sel;
      this.LNKECCPOISONSTAT = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCPOISONSTAT::type_id::create("LNKECCPOISONSTAT",,get_full_name());
      if(this.LNKECCPOISONSTAT.has_coverage(UVM_CVR_REG_BITS))
      	this.LNKECCPOISONSTAT.cg_bits.option.name = {get_name(), ".", "LNKECCPOISONSTAT_bits"};
      this.LNKECCPOISONSTAT.configure(this, null, "");
      this.LNKECCPOISONSTAT.build();
	  uvm_resource_db#(string)::set({"REG::", LNKECCPOISONSTAT.get_full_name()}, "accessType", "NONSECURE", this);
         this.LNKECCPOISONSTAT.add_hdl_path('{
            '{"ddrc_reg_linkecc_poison_complete", 0, 1}
         });
      this.default_map.add_reg(this.LNKECCPOISONSTAT, `UVM_REG_ADDR_WIDTH'h98C, "RO", 0);
		this.LNKECCPOISONSTAT_linkecc_poison_complete = this.LNKECCPOISONSTAT.linkecc_poison_complete;
		this.linkecc_poison_complete = this.LNKECCPOISONSTAT.linkecc_poison_complete;
      this.LNKECCINDEX = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCINDEX::type_id::create("LNKECCINDEX",,get_full_name());
      if(this.LNKECCINDEX.has_coverage(UVM_CVR_REG_BITS))
      	this.LNKECCINDEX.cg_bits.option.name = {get_name(), ".", "LNKECCINDEX_bits"};
      this.LNKECCINDEX.configure(this, null, "");
      this.LNKECCINDEX.build();
	  uvm_resource_db#(string)::set({"REG::", LNKECCINDEX.get_full_name()}, "accessType", "NONSECURE", this);
         this.LNKECCINDEX.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rd_link_ecc_err_byte_sel", 0, 3},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rd_link_ecc_err_rank_sel", 4, 2}
         });
      this.default_map.add_reg(this.LNKECCINDEX, `UVM_REG_ADDR_WIDTH'h990, "RW", 0);
		this.LNKECCINDEX_rd_link_ecc_err_byte_sel = this.LNKECCINDEX.rd_link_ecc_err_byte_sel;
		this.rd_link_ecc_err_byte_sel = this.LNKECCINDEX.rd_link_ecc_err_byte_sel;
		this.LNKECCINDEX_rd_link_ecc_err_rank_sel = this.LNKECCINDEX.rd_link_ecc_err_rank_sel;
		this.rd_link_ecc_err_rank_sel = this.LNKECCINDEX.rd_link_ecc_err_rank_sel;
      this.LNKECCERRCNT0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCERRCNT0::type_id::create("LNKECCERRCNT0",,get_full_name());
      if(this.LNKECCERRCNT0.has_coverage(UVM_CVR_REG_BITS))
      	this.LNKECCERRCNT0.cg_bits.option.name = {get_name(), ".", "LNKECCERRCNT0_bits"};
      this.LNKECCERRCNT0.configure(this, null, "");
      this.LNKECCERRCNT0.build();
	  uvm_resource_db#(string)::set({"REG::", LNKECCERRCNT0.get_full_name()}, "accessType", "NONSECURE", this);
         this.LNKECCERRCNT0.add_hdl_path('{
            '{"ddrc_reg_rd_link_ecc_err_syndrome", 0, 9},
            '{"ddrc_reg_rd_link_ecc_corr_cnt", 16, 8},
            '{"ddrc_reg_rd_link_ecc_uncorr_cnt", 24, 8}
         });
      this.default_map.add_reg(this.LNKECCERRCNT0, `UVM_REG_ADDR_WIDTH'h994, "RO", 0);
		this.LNKECCERRCNT0_rd_link_ecc_err_syndrome = this.LNKECCERRCNT0.rd_link_ecc_err_syndrome;
		this.rd_link_ecc_err_syndrome = this.LNKECCERRCNT0.rd_link_ecc_err_syndrome;
		this.LNKECCERRCNT0_rd_link_ecc_corr_cnt = this.LNKECCERRCNT0.rd_link_ecc_corr_cnt;
		this.rd_link_ecc_corr_cnt = this.LNKECCERRCNT0.rd_link_ecc_corr_cnt;
		this.LNKECCERRCNT0_rd_link_ecc_uncorr_cnt = this.LNKECCERRCNT0.rd_link_ecc_uncorr_cnt;
		this.rd_link_ecc_uncorr_cnt = this.LNKECCERRCNT0.rd_link_ecc_uncorr_cnt;
      this.LNKECCERRSTAT = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCERRSTAT::type_id::create("LNKECCERRSTAT",,get_full_name());
      if(this.LNKECCERRSTAT.has_coverage(UVM_CVR_REG_BITS))
      	this.LNKECCERRSTAT.cg_bits.option.name = {get_name(), ".", "LNKECCERRSTAT_bits"};
      this.LNKECCERRSTAT.configure(this, null, "");
      this.LNKECCERRSTAT.build();
	  uvm_resource_db#(string)::set({"REG::", LNKECCERRSTAT.get_full_name()}, "accessType", "NONSECURE", this);
         this.LNKECCERRSTAT.add_hdl_path('{
            '{"ddrc_reg_rd_link_ecc_corr_err_int", 0, 4},
            '{"ddrc_reg_rd_link_ecc_uncorr_err_int", 8, 4}
         });
      this.default_map.add_reg(this.LNKECCERRSTAT, `UVM_REG_ADDR_WIDTH'h998, "RO", 0);
		this.LNKECCERRSTAT_rd_link_ecc_corr_err_int = this.LNKECCERRSTAT.rd_link_ecc_corr_err_int;
		this.rd_link_ecc_corr_err_int = this.LNKECCERRSTAT.rd_link_ecc_corr_err_int;
		this.LNKECCERRSTAT_rd_link_ecc_uncorr_err_int = this.LNKECCERRSTAT.rd_link_ecc_uncorr_err_int;
		this.rd_link_ecc_uncorr_err_int = this.LNKECCERRSTAT.rd_link_ecc_uncorr_err_int;
      this.LNKECCCADDR0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCCADDR0::type_id::create("LNKECCCADDR0",,get_full_name());
      if(this.LNKECCCADDR0.has_coverage(UVM_CVR_REG_BITS))
      	this.LNKECCCADDR0.cg_bits.option.name = {get_name(), ".", "LNKECCCADDR0_bits"};
      this.LNKECCCADDR0.configure(this, null, "");
      this.LNKECCCADDR0.build();
	  uvm_resource_db#(string)::set({"REG::", LNKECCCADDR0.get_full_name()}, "accessType", "NONSECURE", this);
         this.LNKECCCADDR0.add_hdl_path('{
            '{"ddrc_reg_link_ecc_corr_row", 0, 18},
            '{"ddrc_reg_link_ecc_corr_rank", 24, 1}
         });
      this.default_map.add_reg(this.LNKECCCADDR0, `UVM_REG_ADDR_WIDTH'h9E0, "RO", 0);
		this.LNKECCCADDR0_link_ecc_corr_row = this.LNKECCCADDR0.link_ecc_corr_row;
		this.link_ecc_corr_row = this.LNKECCCADDR0.link_ecc_corr_row;
		this.LNKECCCADDR0_link_ecc_corr_rank = this.LNKECCCADDR0.link_ecc_corr_rank;
		this.link_ecc_corr_rank = this.LNKECCCADDR0.link_ecc_corr_rank;
      this.LNKECCCADDR1 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCCADDR1::type_id::create("LNKECCCADDR1",,get_full_name());
      if(this.LNKECCCADDR1.has_coverage(UVM_CVR_REG_BITS))
      	this.LNKECCCADDR1.cg_bits.option.name = {get_name(), ".", "LNKECCCADDR1_bits"};
      this.LNKECCCADDR1.configure(this, null, "");
      this.LNKECCCADDR1.build();
	  uvm_resource_db#(string)::set({"REG::", LNKECCCADDR1.get_full_name()}, "accessType", "NONSECURE", this);
         this.LNKECCCADDR1.add_hdl_path('{
            '{"ddrc_reg_link_ecc_corr_col", 0, 11},
            '{"ddrc_reg_link_ecc_corr_bank", 16, 3},
            '{"ddrc_reg_link_ecc_corr_bg", 24, 2}
         });
      this.default_map.add_reg(this.LNKECCCADDR1, `UVM_REG_ADDR_WIDTH'h9E4, "RO", 0);
		this.LNKECCCADDR1_link_ecc_corr_col = this.LNKECCCADDR1.link_ecc_corr_col;
		this.link_ecc_corr_col = this.LNKECCCADDR1.link_ecc_corr_col;
		this.LNKECCCADDR1_link_ecc_corr_bank = this.LNKECCCADDR1.link_ecc_corr_bank;
		this.link_ecc_corr_bank = this.LNKECCCADDR1.link_ecc_corr_bank;
		this.LNKECCCADDR1_link_ecc_corr_bg = this.LNKECCCADDR1.link_ecc_corr_bg;
		this.link_ecc_corr_bg = this.LNKECCCADDR1.link_ecc_corr_bg;
      this.LNKECCUADDR0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCUADDR0::type_id::create("LNKECCUADDR0",,get_full_name());
      if(this.LNKECCUADDR0.has_coverage(UVM_CVR_REG_BITS))
      	this.LNKECCUADDR0.cg_bits.option.name = {get_name(), ".", "LNKECCUADDR0_bits"};
      this.LNKECCUADDR0.configure(this, null, "");
      this.LNKECCUADDR0.build();
	  uvm_resource_db#(string)::set({"REG::", LNKECCUADDR0.get_full_name()}, "accessType", "NONSECURE", this);
         this.LNKECCUADDR0.add_hdl_path('{
            '{"ddrc_reg_link_ecc_uncorr_row", 0, 18},
            '{"ddrc_reg_link_ecc_uncorr_rank", 24, 1}
         });
      this.default_map.add_reg(this.LNKECCUADDR0, `UVM_REG_ADDR_WIDTH'h9E8, "RO", 0);
		this.LNKECCUADDR0_link_ecc_uncorr_row = this.LNKECCUADDR0.link_ecc_uncorr_row;
		this.link_ecc_uncorr_row = this.LNKECCUADDR0.link_ecc_uncorr_row;
		this.LNKECCUADDR0_link_ecc_uncorr_rank = this.LNKECCUADDR0.link_ecc_uncorr_rank;
		this.link_ecc_uncorr_rank = this.LNKECCUADDR0.link_ecc_uncorr_rank;
      this.LNKECCUADDR1 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_LNKECCUADDR1::type_id::create("LNKECCUADDR1",,get_full_name());
      if(this.LNKECCUADDR1.has_coverage(UVM_CVR_REG_BITS))
      	this.LNKECCUADDR1.cg_bits.option.name = {get_name(), ".", "LNKECCUADDR1_bits"};
      this.LNKECCUADDR1.configure(this, null, "");
      this.LNKECCUADDR1.build();
	  uvm_resource_db#(string)::set({"REG::", LNKECCUADDR1.get_full_name()}, "accessType", "NONSECURE", this);
         this.LNKECCUADDR1.add_hdl_path('{
            '{"ddrc_reg_link_ecc_uncorr_col", 0, 11},
            '{"ddrc_reg_link_ecc_uncorr_bank", 16, 3},
            '{"ddrc_reg_link_ecc_uncorr_bg", 24, 2}
         });
      this.default_map.add_reg(this.LNKECCUADDR1, `UVM_REG_ADDR_WIDTH'h9EC, "RO", 0);
		this.LNKECCUADDR1_link_ecc_uncorr_col = this.LNKECCUADDR1.link_ecc_uncorr_col;
		this.link_ecc_uncorr_col = this.LNKECCUADDR1.link_ecc_uncorr_col;
		this.LNKECCUADDR1_link_ecc_uncorr_bank = this.LNKECCUADDR1.link_ecc_uncorr_bank;
		this.link_ecc_uncorr_bank = this.LNKECCUADDR1.link_ecc_uncorr_bank;
		this.LNKECCUADDR1_link_ecc_uncorr_bg = this.LNKECCUADDR1.link_ecc_uncorr_bg;
		this.link_ecc_uncorr_bg = this.LNKECCUADDR1.link_ecc_uncorr_bg;
      this.OPCTRL0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRL0::type_id::create("OPCTRL0",,get_full_name());
      if(this.OPCTRL0.has_coverage(UVM_CVR_REG_BITS))
      	this.OPCTRL0.cg_bits.option.name = {get_name(), ".", "OPCTRL0_bits"};
      this.OPCTRL0.configure(this, null, "");
      this.OPCTRL0.build();
	  uvm_resource_db#(string)::set({"REG::", OPCTRL0.get_full_name()}, "accessType", "NONSECURE", this);
         this.OPCTRL0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_dis_wc", 0, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_dis_max_rank_rd_opt", 6, 1},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_dis_max_rank_wr_opt", 7, 1}
         });
      this.default_map.add_reg(this.OPCTRL0, `UVM_REG_ADDR_WIDTH'hB80, "RW", 0);
		this.OPCTRL0_dis_wc = this.OPCTRL0.dis_wc;
		this.dis_wc = this.OPCTRL0.dis_wc;
		this.OPCTRL0_dis_max_rank_rd_opt = this.OPCTRL0.dis_max_rank_rd_opt;
		this.dis_max_rank_rd_opt = this.OPCTRL0.dis_max_rank_rd_opt;
		this.OPCTRL0_dis_max_rank_wr_opt = this.OPCTRL0.dis_max_rank_wr_opt;
		this.dis_max_rank_wr_opt = this.OPCTRL0.dis_max_rank_wr_opt;
      this.OPCTRL1 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRL1::type_id::create("OPCTRL1",,get_full_name());
      if(this.OPCTRL1.has_coverage(UVM_CVR_REG_BITS))
      	this.OPCTRL1.cg_bits.option.name = {get_name(), ".", "OPCTRL1_bits"};
      this.OPCTRL1.configure(this, null, "");
      this.OPCTRL1.build();
	  uvm_resource_db#(string)::set({"REG::", OPCTRL1.get_full_name()}, "accessType", "NONSECURE", this);
         this.OPCTRL1.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dis_dq", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dis_hif", 1, 1}
         });
      this.default_map.add_reg(this.OPCTRL1, `UVM_REG_ADDR_WIDTH'hB84, "RW", 0);
		this.OPCTRL1_dis_dq = this.OPCTRL1.dis_dq;
		this.dis_dq = this.OPCTRL1.dis_dq;
		this.OPCTRL1_dis_hif = this.OPCTRL1.dis_hif;
		this.dis_hif = this.OPCTRL1.dis_hif;
      this.OPCTRLCAM = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLCAM::type_id::create("OPCTRLCAM",,get_full_name());
      if(this.OPCTRLCAM.has_coverage(UVM_CVR_REG_BITS))
      	this.OPCTRLCAM.cg_bits.option.name = {get_name(), ".", "OPCTRLCAM_bits"};
      this.OPCTRLCAM.configure(this, null, "");
      this.OPCTRLCAM.build();
	  uvm_resource_db#(string)::set({"REG::", OPCTRLCAM.get_full_name()}, "accessType", "NONSECURE", this);
         this.OPCTRLCAM.add_hdl_path('{
            '{"ddrc_reg_dbg_hpr_q_depth", 0, 7},
            '{"ddrc_reg_dbg_lpr_q_depth", 8, 7},
            '{"ddrc_reg_dbg_w_q_depth", 16, 7},
            '{"ddrc_reg_dbg_stall", 24, 1},
            '{"ddrc_reg_dbg_rd_q_empty", 25, 1},
            '{"ddrc_reg_dbg_wr_q_empty", 26, 1},
            '{"ddrc_reg_rd_data_pipeline_empty", 28, 1},
            '{"ddrc_reg_wr_data_pipeline_empty", 29, 1}
         });
      this.default_map.add_reg(this.OPCTRLCAM, `UVM_REG_ADDR_WIDTH'hB88, "RO", 0);
		this.OPCTRLCAM_dbg_hpr_q_depth = this.OPCTRLCAM.dbg_hpr_q_depth;
		this.dbg_hpr_q_depth = this.OPCTRLCAM.dbg_hpr_q_depth;
		this.OPCTRLCAM_dbg_lpr_q_depth = this.OPCTRLCAM.dbg_lpr_q_depth;
		this.dbg_lpr_q_depth = this.OPCTRLCAM.dbg_lpr_q_depth;
		this.OPCTRLCAM_dbg_w_q_depth = this.OPCTRLCAM.dbg_w_q_depth;
		this.dbg_w_q_depth = this.OPCTRLCAM.dbg_w_q_depth;
		this.OPCTRLCAM_dbg_stall = this.OPCTRLCAM.dbg_stall;
		this.dbg_stall = this.OPCTRLCAM.dbg_stall;
		this.OPCTRLCAM_dbg_rd_q_empty = this.OPCTRLCAM.dbg_rd_q_empty;
		this.dbg_rd_q_empty = this.OPCTRLCAM.dbg_rd_q_empty;
		this.OPCTRLCAM_dbg_wr_q_empty = this.OPCTRLCAM.dbg_wr_q_empty;
		this.dbg_wr_q_empty = this.OPCTRLCAM.dbg_wr_q_empty;
		this.OPCTRLCAM_rd_data_pipeline_empty = this.OPCTRLCAM.rd_data_pipeline_empty;
		this.rd_data_pipeline_empty = this.OPCTRLCAM.rd_data_pipeline_empty;
		this.OPCTRLCAM_wr_data_pipeline_empty = this.OPCTRLCAM.wr_data_pipeline_empty;
		this.wr_data_pipeline_empty = this.OPCTRLCAM.wr_data_pipeline_empty;
      this.OPCTRLCMD = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLCMD::type_id::create("OPCTRLCMD",,get_full_name());
      if(this.OPCTRLCMD.has_coverage(UVM_CVR_REG_BITS))
      	this.OPCTRLCMD.cg_bits.option.name = {get_name(), ".", "OPCTRLCMD_bits"};
      this.OPCTRLCMD.configure(this, null, "");
      this.OPCTRLCMD.build();
	  uvm_resource_db#(bit)::set({"REG::", OPCTRLCMD.get_full_name()}, "NO_REG_BIT_BASH_TEST", 1, this);
	  uvm_resource_db#(string)::set({"REG::", OPCTRLCMD.get_full_name()}, "accessType", "NONSECURE", this);
         this.OPCTRLCMD.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_zq_calib_short", 16, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ctrlupd", 17, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ctrlupd_burst", 18, 1}
         });
      this.default_map.add_reg(this.OPCTRLCMD, `UVM_REG_ADDR_WIDTH'hB8C, "RW", 0);
		this.OPCTRLCMD_zq_calib_short = this.OPCTRLCMD.zq_calib_short;
		this.zq_calib_short = this.OPCTRLCMD.zq_calib_short;
		this.OPCTRLCMD_ctrlupd = this.OPCTRLCMD.ctrlupd;
		this.ctrlupd = this.OPCTRLCMD.ctrlupd;
		this.OPCTRLCMD_ctrlupd_burst = this.OPCTRLCMD.ctrlupd_burst;
		this.ctrlupd_burst = this.OPCTRLCMD.ctrlupd_burst;
      this.OPCTRLSTAT = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLSTAT::type_id::create("OPCTRLSTAT",,get_full_name());
      if(this.OPCTRLSTAT.has_coverage(UVM_CVR_REG_BITS))
      	this.OPCTRLSTAT.cg_bits.option.name = {get_name(), ".", "OPCTRLSTAT_bits"};
      this.OPCTRLSTAT.configure(this, null, "");
      this.OPCTRLSTAT.build();
	  uvm_resource_db#(string)::set({"REG::", OPCTRLSTAT.get_full_name()}, "accessType", "NONSECURE", this);
         this.OPCTRLSTAT.add_hdl_path('{
            '{"ddrc_reg_zq_calib_short_busy", 16, 1},
            '{"ddrc_reg_ctrlupd_busy", 17, 1},
            '{"ddrc_reg_ctrlupd_burst_busy", 18, 1}
         });
      this.default_map.add_reg(this.OPCTRLSTAT, `UVM_REG_ADDR_WIDTH'hB90, "RO", 0);
		this.OPCTRLSTAT_zq_calib_short_busy = this.OPCTRLSTAT.zq_calib_short_busy;
		this.zq_calib_short_busy = this.OPCTRLSTAT.zq_calib_short_busy;
		this.OPCTRLSTAT_ctrlupd_busy = this.OPCTRLSTAT.ctrlupd_busy;
		this.ctrlupd_busy = this.OPCTRLSTAT.ctrlupd_busy;
		this.OPCTRLSTAT_ctrlupd_burst_busy = this.OPCTRLSTAT.ctrlupd_burst_busy;
		this.ctrlupd_burst_busy = this.OPCTRLSTAT.ctrlupd_burst_busy;
      this.OPCTRLCAM1 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRLCAM1::type_id::create("OPCTRLCAM1",,get_full_name());
      if(this.OPCTRLCAM1.has_coverage(UVM_CVR_REG_BITS))
      	this.OPCTRLCAM1.cg_bits.option.name = {get_name(), ".", "OPCTRLCAM1_bits"};
      this.OPCTRLCAM1.configure(this, null, "");
      this.OPCTRLCAM1.build();
	  uvm_resource_db#(string)::set({"REG::", OPCTRLCAM1.get_full_name()}, "accessType", "NONSECURE", this);
         this.OPCTRLCAM1.add_hdl_path('{
            '{"ddrc_reg_dbg_wrecc_q_depth", 0, 7}
         });
      this.default_map.add_reg(this.OPCTRLCAM1, `UVM_REG_ADDR_WIDTH'hB94, "RO", 0);
		this.OPCTRLCAM1_dbg_wrecc_q_depth = this.OPCTRLCAM1.dbg_wrecc_q_depth;
		this.dbg_wrecc_q_depth = this.OPCTRLCAM1.dbg_wrecc_q_depth;
      this.OPREFCTRL0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPREFCTRL0::type_id::create("OPREFCTRL0",,get_full_name());
      if(this.OPREFCTRL0.has_coverage(UVM_CVR_REG_BITS))
      	this.OPREFCTRL0.cg_bits.option.name = {get_name(), ".", "OPREFCTRL0_bits"};
      this.OPREFCTRL0.configure(this, null, "");
      this.OPREFCTRL0.build();
	  uvm_resource_db#(bit)::set({"REG::", OPREFCTRL0.get_full_name()}, "NO_REG_BIT_BASH_TEST", 1, this);
	  uvm_resource_db#(string)::set({"REG::", OPREFCTRL0.get_full_name()}, "accessType", "NONSECURE", this);
         this.OPREFCTRL0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rank0_refresh", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rank1_refresh", 1, 1}
         });
      this.default_map.add_reg(this.OPREFCTRL0, `UVM_REG_ADDR_WIDTH'hB98, "RW", 0);
		this.OPREFCTRL0_rank0_refresh = this.OPREFCTRL0.rank0_refresh;
		this.rank0_refresh = this.OPREFCTRL0.rank0_refresh;
		this.OPREFCTRL0_rank1_refresh = this.OPREFCTRL0.rank1_refresh;
		this.rank1_refresh = this.OPREFCTRL0.rank1_refresh;
      this.OPREFSTAT0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_OPREFSTAT0::type_id::create("OPREFSTAT0",,get_full_name());
      if(this.OPREFSTAT0.has_coverage(UVM_CVR_REG_BITS))
      	this.OPREFSTAT0.cg_bits.option.name = {get_name(), ".", "OPREFSTAT0_bits"};
      this.OPREFSTAT0.configure(this, null, "");
      this.OPREFSTAT0.build();
	  uvm_resource_db#(string)::set({"REG::", OPREFSTAT0.get_full_name()}, "accessType", "NONSECURE", this);
         this.OPREFSTAT0.add_hdl_path('{
            '{"ddrc_reg_rank0_refresh_busy", 0, 1},
            '{"ddrc_reg_rank1_refresh_busy", 1, 1}
         });
      this.default_map.add_reg(this.OPREFSTAT0, `UVM_REG_ADDR_WIDTH'hBA0, "RO", 0);
		this.OPREFSTAT0_rank0_refresh_busy = this.OPREFSTAT0.rank0_refresh_busy;
		this.rank0_refresh_busy = this.OPREFSTAT0.rank0_refresh_busy;
		this.OPREFSTAT0_rank1_refresh_busy = this.OPREFSTAT0.rank1_refresh_busy;
		this.rank1_refresh_busy = this.OPREFSTAT0.rank1_refresh_busy;
      this.SWCTL = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SWCTL::type_id::create("SWCTL",,get_full_name());
      if(this.SWCTL.has_coverage(UVM_CVR_REG_BITS))
      	this.SWCTL.cg_bits.option.name = {get_name(), ".", "SWCTL_bits"};
      this.SWCTL.configure(this, null, "");
      this.SWCTL.build();
	  uvm_resource_db#(string)::set({"REG::", SWCTL.get_full_name()}, "accessType", "NONSECURE", this);
         this.SWCTL.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_sw_done", 0, 1}
         });
      this.default_map.add_reg(this.SWCTL, `UVM_REG_ADDR_WIDTH'hC80, "RW", 0);
		this.SWCTL_sw_done = this.SWCTL.sw_done;
		this.sw_done = this.SWCTL.sw_done;
      this.SWSTAT = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SWSTAT::type_id::create("SWSTAT",,get_full_name());
      if(this.SWSTAT.has_coverage(UVM_CVR_REG_BITS))
      	this.SWSTAT.cg_bits.option.name = {get_name(), ".", "SWSTAT_bits"};
      this.SWSTAT.configure(this, null, "");
      this.SWSTAT.build();
	  uvm_resource_db#(string)::set({"REG::", SWSTAT.get_full_name()}, "accessType", "NONSECURE", this);
         this.SWSTAT.add_hdl_path('{
            '{"ddrc_reg_sw_done_ack", 0, 1}
         });
      this.default_map.add_reg(this.SWSTAT, `UVM_REG_ADDR_WIDTH'hC84, "RO", 0);
		this.SWSTAT_sw_done_ack = this.SWSTAT.sw_done_ack;
		this.sw_done_ack = this.SWSTAT.sw_done_ack;
      this.RANKCTL = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_RANKCTL::type_id::create("RANKCTL",,get_full_name());
      if(this.RANKCTL.has_coverage(UVM_CVR_REG_BITS))
      	this.RANKCTL.cg_bits.option.name = {get_name(), ".", "RANKCTL_bits"};
      this.RANKCTL.configure(this, null, "");
      this.RANKCTL.build();
	  uvm_resource_db#(string)::set({"REG::", RANKCTL.get_full_name()}, "accessType", "NONSECURE", this);
         this.RANKCTL.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_max_rank_rd", 0, 4},
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_max_rank_wr", 12, 4}
         });
      this.default_map.add_reg(this.RANKCTL, `UVM_REG_ADDR_WIDTH'hC90, "RW", 0);
		this.RANKCTL_max_rank_rd = this.RANKCTL.max_rank_rd;
		this.max_rank_rd = this.RANKCTL.max_rank_rd;
		this.RANKCTL_max_rank_wr = this.RANKCTL.max_rank_wr;
		this.max_rank_wr = this.RANKCTL.max_rank_wr;
      this.DBICTL = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DBICTL::type_id::create("DBICTL",,get_full_name());
      if(this.DBICTL.has_coverage(UVM_CVR_REG_BITS))
      	this.DBICTL.cg_bits.option.name = {get_name(), ".", "DBICTL_bits"};
      this.DBICTL.configure(this, null, "");
      this.DBICTL.build();
	  uvm_resource_db#(string)::set({"REG::", DBICTL.get_full_name()}, "accessType", "NONSECURE", this);
         this.DBICTL.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_dm_en", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_wr_dbi_en", 1, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rd_dbi_en", 2, 1}
         });
      this.default_map.add_reg(this.DBICTL, `UVM_REG_ADDR_WIDTH'hC94, "RW", 0);
		this.DBICTL_dm_en = this.DBICTL.dm_en;
		this.dm_en = this.DBICTL.dm_en;
		this.DBICTL_wr_dbi_en = this.DBICTL.wr_dbi_en;
		this.wr_dbi_en = this.DBICTL.wr_dbi_en;
		this.DBICTL_rd_dbi_en = this.DBICTL.rd_dbi_en;
		this.rd_dbi_en = this.DBICTL.rd_dbi_en;
      this.ODTMAP = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_ODTMAP::type_id::create("ODTMAP",,get_full_name());
      if(this.ODTMAP.has_coverage(UVM_CVR_REG_BITS))
      	this.ODTMAP.cg_bits.option.name = {get_name(), ".", "ODTMAP_bits"};
      this.ODTMAP.configure(this, null, "");
      this.ODTMAP.build();
	  uvm_resource_db#(string)::set({"REG::", ODTMAP.get_full_name()}, "accessType", "NONSECURE", this);
         this.ODTMAP.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rank0_wr_odt", 0, 2},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rank0_rd_odt", 4, 2},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rank1_wr_odt", 8, 2},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rank1_rd_odt", 12, 2}
         });
      this.default_map.add_reg(this.ODTMAP, `UVM_REG_ADDR_WIDTH'hC9C, "RW", 0);
		this.ODTMAP_rank0_wr_odt = this.ODTMAP.rank0_wr_odt;
		this.rank0_wr_odt = this.ODTMAP.rank0_wr_odt;
		this.ODTMAP_rank0_rd_odt = this.ODTMAP.rank0_rd_odt;
		this.rank0_rd_odt = this.ODTMAP.rank0_rd_odt;
		this.ODTMAP_rank1_wr_odt = this.ODTMAP.rank1_wr_odt;
		this.rank1_wr_odt = this.ODTMAP.rank1_wr_odt;
		this.ODTMAP_rank1_rd_odt = this.ODTMAP.rank1_rd_odt;
		this.rank1_rd_odt = this.ODTMAP.rank1_rd_odt;
      this.DATACTL0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DATACTL0::type_id::create("DATACTL0",,get_full_name());
      if(this.DATACTL0.has_coverage(UVM_CVR_REG_BITS))
      	this.DATACTL0.cg_bits.option.name = {get_name(), ".", "DATACTL0_bits"};
      this.DATACTL0.configure(this, null, "");
      this.DATACTL0.build();
	  uvm_resource_db#(string)::set({"REG::", DATACTL0.get_full_name()}, "accessType", "NONSECURE", this);
         this.DATACTL0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_rd_data_copy_en", 16, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_wr_data_copy_en", 17, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_wr_data_x_en", 18, 1}
         });
      this.default_map.add_reg(this.DATACTL0, `UVM_REG_ADDR_WIDTH'hCA0, "RW", 0);
		this.DATACTL0_rd_data_copy_en = this.DATACTL0.rd_data_copy_en;
		this.rd_data_copy_en = this.DATACTL0.rd_data_copy_en;
		this.DATACTL0_wr_data_copy_en = this.DATACTL0.wr_data_copy_en;
		this.wr_data_copy_en = this.DATACTL0.wr_data_copy_en;
		this.DATACTL0_wr_data_x_en = this.DATACTL0.wr_data_x_en;
		this.wr_data_x_en = this.DATACTL0.wr_data_x_en;
      this.SWCTLSTATIC = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_SWCTLSTATIC::type_id::create("SWCTLSTATIC",,get_full_name());
      if(this.SWCTLSTATIC.has_coverage(UVM_CVR_REG_BITS))
      	this.SWCTLSTATIC.cg_bits.option.name = {get_name(), ".", "SWCTLSTATIC_bits"};
      this.SWCTLSTATIC.configure(this, null, "");
      this.SWCTLSTATIC.build();
	  uvm_resource_db#(string)::set({"REG::", SWCTLSTATIC.get_full_name()}, "accessType", "NONSECURE", this);
         this.SWCTLSTATIC.add_hdl_path('{
            '{"U_apb_slvtop.slvif.cfgs_ff_regb_ddrc_ch0_sw_static_unlock", 0, 1}
         });
      this.default_map.add_reg(this.SWCTLSTATIC, `UVM_REG_ADDR_WIDTH'hCA4, "RW", 0);
		this.SWCTLSTATIC_sw_static_unlock = this.SWCTLSTATIC.sw_static_unlock;
		this.sw_static_unlock = this.SWCTLSTATIC.sw_static_unlock;
      this.CGCTL = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_CGCTL::type_id::create("CGCTL",,get_full_name());
      if(this.CGCTL.has_coverage(UVM_CVR_REG_BITS))
      	this.CGCTL.cg_bits.option.name = {get_name(), ".", "CGCTL_bits"};
      this.CGCTL.configure(this, null, "");
      this.CGCTL.build();
         this.CGCTL.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_force_clk_te_en", 0, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_force_clk_arb_en", 4, 1}
         });
      this.default_map.add_reg(this.CGCTL, `UVM_REG_ADDR_WIDTH'hCB0, "RW", 0);
		this.CGCTL_force_clk_te_en = this.CGCTL.force_clk_te_en;
		this.force_clk_te_en = this.CGCTL.force_clk_te_en;
		this.CGCTL_force_clk_arb_en = this.CGCTL.force_clk_arb_en;
		this.force_clk_arb_en = this.CGCTL.force_clk_arb_en;
      this.INITTMG0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_INITTMG0::type_id::create("INITTMG0",,get_full_name());
      if(this.INITTMG0.has_coverage(UVM_CVR_REG_BITS))
      	this.INITTMG0.cg_bits.option.name = {get_name(), ".", "INITTMG0_bits"};
      this.INITTMG0.configure(this, null, "");
      this.INITTMG0.build();
	  uvm_resource_db#(string)::set({"REG::", INITTMG0.get_full_name()}, "accessType", "NONSECURE", this);
         this.INITTMG0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_pre_cke_x1024", 0, 13},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_post_cke_x1024", 16, 10},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_skip_dram_init", 30, 2}
         });
      this.default_map.add_reg(this.INITTMG0, `UVM_REG_ADDR_WIDTH'hD00, "RW", 0);
		this.INITTMG0_pre_cke_x1024 = this.INITTMG0.pre_cke_x1024;
		this.pre_cke_x1024 = this.INITTMG0.pre_cke_x1024;
		this.INITTMG0_post_cke_x1024 = this.INITTMG0.post_cke_x1024;
		this.post_cke_x1024 = this.INITTMG0.post_cke_x1024;
		this.INITTMG0_skip_dram_init = this.INITTMG0.skip_dram_init;
		this.skip_dram_init = this.INITTMG0.skip_dram_init;
      this.PPT2CTRL0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_PPT2CTRL0::type_id::create("PPT2CTRL0",,get_full_name());
      if(this.PPT2CTRL0.has_coverage(UVM_CVR_REG_BITS))
      	this.PPT2CTRL0.cg_bits.option.name = {get_name(), ".", "PPT2CTRL0_bits"};
      this.PPT2CTRL0.configure(this, null, "");
      this.PPT2CTRL0.build();
	  uvm_resource_db#(bit)::set({"REG::", PPT2CTRL0.get_full_name()}, "NO_REG_BIT_BASH_TEST", 1, this);
	  uvm_resource_db#(string)::set({"REG::", PPT2CTRL0.get_full_name()}, "accessType", "NONSECURE", this);
         this.PPT2CTRL0.add_hdl_path('{
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ppt2_burst_num", 0, 10},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ppt2_ctrlupd_num_dfi0", 12, 6},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ppt2_ctrlupd_num_dfi1", 18, 6},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ppt2_burst", 28, 1},
            '{"U_apb_slvtop.slvif.ff_regb_ddrc_ch0_ppt2_wait_ref", 31, 1}
         });
      this.default_map.add_reg(this.PPT2CTRL0, `UVM_REG_ADDR_WIDTH'hF00, "RW", 0);
		this.PPT2CTRL0_ppt2_burst_num = this.PPT2CTRL0.ppt2_burst_num;
		this.ppt2_burst_num = this.PPT2CTRL0.ppt2_burst_num;
		this.PPT2CTRL0_ppt2_ctrlupd_num_dfi0 = this.PPT2CTRL0.ppt2_ctrlupd_num_dfi0;
		this.ppt2_ctrlupd_num_dfi0 = this.PPT2CTRL0.ppt2_ctrlupd_num_dfi0;
		this.PPT2CTRL0_ppt2_ctrlupd_num_dfi1 = this.PPT2CTRL0.ppt2_ctrlupd_num_dfi1;
		this.ppt2_ctrlupd_num_dfi1 = this.PPT2CTRL0.ppt2_ctrlupd_num_dfi1;
		this.PPT2CTRL0_ppt2_burst = this.PPT2CTRL0.ppt2_burst;
		this.ppt2_burst = this.PPT2CTRL0.ppt2_burst;
		this.PPT2CTRL0_ppt2_wait_ref = this.PPT2CTRL0.ppt2_wait_ref;
		this.ppt2_wait_ref = this.PPT2CTRL0.ppt2_wait_ref;
      this.PPT2STAT0 = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_PPT2STAT0::type_id::create("PPT2STAT0",,get_full_name());
      if(this.PPT2STAT0.has_coverage(UVM_CVR_REG_BITS))
      	this.PPT2STAT0.cg_bits.option.name = {get_name(), ".", "PPT2STAT0_bits"};
      this.PPT2STAT0.configure(this, null, "");
      this.PPT2STAT0.build();
	  uvm_resource_db#(string)::set({"REG::", PPT2STAT0.get_full_name()}, "accessType", "NONSECURE", this);
         this.PPT2STAT0.add_hdl_path('{
            '{"ddrc_reg_ppt2_state", 0, 4},
            '{"ddrc_reg_ppt2_burst_busy", 28, 1}
         });
      this.default_map.add_reg(this.PPT2STAT0, `UVM_REG_ADDR_WIDTH'hF10, "RO", 0);
		this.PPT2STAT0_ppt2_state = this.PPT2STAT0.ppt2_state;
		this.ppt2_state = this.PPT2STAT0.ppt2_state;
		this.PPT2STAT0_ppt2_burst_busy = this.PPT2STAT0.ppt2_burst_busy;
		this.ppt2_burst_busy = this.PPT2STAT0.ppt2_burst_busy;
      this.DDRCTL_VER_NUMBER = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DDRCTL_VER_NUMBER::type_id::create("DDRCTL_VER_NUMBER",,get_full_name());
      if(this.DDRCTL_VER_NUMBER.has_coverage(UVM_CVR_REG_BITS))
      	this.DDRCTL_VER_NUMBER.cg_bits.option.name = {get_name(), ".", "DDRCTL_VER_NUMBER_bits"};
      this.DDRCTL_VER_NUMBER.configure(this, null, "");
      this.DDRCTL_VER_NUMBER.build();
	  uvm_resource_db#(string)::set({"REG::", DDRCTL_VER_NUMBER.get_full_name()}, "accessType", "NONSECURE", this);
         this.DDRCTL_VER_NUMBER.add_hdl_path('{
            '{"ddrc_reg_ver_number", 0, 32}
         });
      this.default_map.add_reg(this.DDRCTL_VER_NUMBER, `UVM_REG_ADDR_WIDTH'hFF8, "RO", 0);
		this.DDRCTL_VER_NUMBER_ver_number = this.DDRCTL_VER_NUMBER.ver_number;
		this.ver_number = this.DDRCTL_VER_NUMBER.ver_number;
      this.DDRCTL_VER_TYPE = ral_reg_DWC_ddrctl_map_REGB_DDRC_CH0_DDRCTL_VER_TYPE::type_id::create("DDRCTL_VER_TYPE",,get_full_name());
      if(this.DDRCTL_VER_TYPE.has_coverage(UVM_CVR_REG_BITS))
      	this.DDRCTL_VER_TYPE.cg_bits.option.name = {get_name(), ".", "DDRCTL_VER_TYPE_bits"};
      this.DDRCTL_VER_TYPE.configure(this, null, "");
      this.DDRCTL_VER_TYPE.build();
	  uvm_resource_db#(string)::set({"REG::", DDRCTL_VER_TYPE.get_full_name()}, "accessType", "NONSECURE", this);
         this.DDRCTL_VER_TYPE.add_hdl_path('{
            '{"ddrc_reg_ver_type", 0, 32}
         });
      this.default_map.add_reg(this.DDRCTL_VER_TYPE, `UVM_REG_ADDR_WIDTH'hFFC, "RO", 0);
		this.DDRCTL_VER_TYPE_ver_type = this.DDRCTL_VER_TYPE.ver_type;
		this.ver_type = this.DDRCTL_VER_TYPE.ver_type;
   endfunction : build
	`uvm_object_utils(ral_block_DWC_ddrctl_map_REGB_DDRC_CH0)
function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_ddrctl_map_REGB_DDRC_CH0
endpackage
`endif
