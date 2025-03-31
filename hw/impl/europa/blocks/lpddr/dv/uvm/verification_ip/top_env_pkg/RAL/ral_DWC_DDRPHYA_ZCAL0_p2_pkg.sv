`ifndef RAL_DWC_DDRPHYA_ZCAL0_P2_PKG
`define RAL_DWC_DDRPHYA_ZCAL0_P2_PKG

package ral_DWC_DDRPHYA_ZCAL0_p2_pkg;
import uvm_pkg::*;

class ral_reg_DWC_DDRPHYA_ZCAL0_p2_ZCalClkInfo_p2 extends uvm_reg;
	rand uvm_reg_field ZCalDfiClkTicksPer1uS;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalDfiClkTicksPer1uS: coverpoint {m_data[10:0], m_is_read} iff(m_be) {
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p2_ZCalClkInfo_p2");
		super.new(name, 16,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalDfiClkTicksPer1uS = uvm_reg_field::type_id::create("ZCalDfiClkTicksPer1uS",,get_full_name());
      this.ZCalDfiClkTicksPer1uS.configure(this, 11, 0, "RW", 0, 11'h320, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p2_ZCalClkInfo_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p2_ZCalClkInfo_p2


class ral_reg_DWC_DDRPHYA_ZCAL0_p2_PUBReservedP1_p2 extends uvm_reg;
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
	function new(string name = "DWC_DDRPHYA_ZCAL0_p2_PUBReservedP1_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.PUBReservedP1_p2 = uvm_reg_field::type_id::create("PUBReservedP1_p2",,get_full_name());
      this.PUBReservedP1_p2.configure(this, 8, 0, "RW", 0, 8'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p2_PUBReservedP1_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p2_PUBReservedP1_p2


class ral_reg_DWC_DDRPHYA_ZCAL0_p2_ZCalStopClk_p2 extends uvm_reg;
	rand uvm_reg_field ZCalStopClk_p2;
   local uvm_reg_data_t m_data;
   local uvm_reg_data_t m_be;
   local bit            m_is_read;

	covergroup cg_bits ();
	   option.per_instance = 1;
	   option.name = get_name();
	   ZCalStopClk_p2: coverpoint {m_data[0:0], m_is_read} iff(m_be) {
	      wildcard bins bit_0_wr_as_0 = {2'b00};
	      wildcard bins bit_0_wr_as_1 = {2'b10};
	      wildcard bins bit_0_rd_as_0 = {2'b01};
	      wildcard bins bit_0_rd_as_1 = {2'b11};
	      option.weight = 4;
	   }
	endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p2_ZCalStopClk_p2");
		super.new(name, 8,build_coverage(UVM_NO_COVERAGE));
		add_coverage(build_coverage(UVM_NO_COVERAGE));
		if (has_coverage(UVM_CVR_ALL))
			cg_bits = new();
	endfunction: new
   virtual function void build();
      this.ZCalStopClk_p2 = uvm_reg_field::type_id::create("ZCalStopClk_p2",,get_full_name());
      this.ZCalStopClk_p2.configure(this, 1, 0, "RW", 0, 1'h0, 1, 0, 1);
   endfunction: build

	`uvm_object_utils(ral_reg_DWC_DDRPHYA_ZCAL0_p2_ZCalStopClk_p2)

`ifdef UVM_REG_PROTECTED_SAMPLE
    	 protected virtual function void sample(uvm_reg_data_t data,
    	                             uvm_reg_data_t byte_en,
    	                             bit            is_read,
    	                             uvm_reg_map    map);
`else
	 virtual function void sample(uvm_reg_data_t data,
	                             uvm_reg_data_t byte_en,
	                             bit            is_read,
	                             uvm_reg_map    map);
`endif
	   if (get_coverage(UVM_CVR_ALL)) begin
	      m_data    = data;
	      m_be      = byte_en;
	      m_is_read = is_read;
	      cg_bits.sample();
	   end
	endfunction
endclass : ral_reg_DWC_DDRPHYA_ZCAL0_p2_ZCalStopClk_p2


class ral_block_DWC_DDRPHYA_ZCAL0_p2 extends uvm_reg_block;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p2_ZCalClkInfo_p2 ZCalClkInfo_p2;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p2_PUBReservedP1_p2 PUBReservedP1_p2;
	rand ral_reg_DWC_DDRPHYA_ZCAL0_p2_ZCalStopClk_p2 ZCalStopClk_p2;
   local uvm_reg_data_t m_offset;
	rand uvm_reg_field ZCalClkInfo_p2_ZCalDfiClkTicksPer1uS;
	rand uvm_reg_field ZCalDfiClkTicksPer1uS;
	rand uvm_reg_field PUBReservedP1_p2_PUBReservedP1_p2;
	rand uvm_reg_field ZCalStopClk_p2_ZCalStopClk_p2;


	covergroup cg_addr (input string name);
	option.per_instance = 1;
option.name = get_name();

	ZCalClkInfo_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h4 };
		option.weight = 1;
	}

	PUBReservedP1_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'hFF };
		option.weight = 1;
	}

	ZCalStopClk_p2 : coverpoint m_offset {
		bins accessed = { `UVM_REG_ADDR_WIDTH'h32F };
		option.weight = 1;
	}
endgroup
	function new(string name = "DWC_DDRPHYA_ZCAL0_p2");
		super.new(name, build_coverage(UVM_CVR_ADDR_MAP));
		add_coverage(build_coverage(UVM_CVR_ADDR_MAP));
		if (has_coverage(UVM_CVR_ADDR_MAP))
			cg_addr = new("cg_addr");
	endfunction: new

   virtual function void build();
      this.default_map = create_map("", 0, 4, UVM_LITTLE_ENDIAN, 0);
      this.ZCalClkInfo_p2 = ral_reg_DWC_DDRPHYA_ZCAL0_p2_ZCalClkInfo_p2::type_id::create("ZCalClkInfo_p2",,get_full_name());
      if(this.ZCalClkInfo_p2.has_coverage(UVM_CVR_ALL))
      	this.ZCalClkInfo_p2.cg_bits.option.name = {get_name(), ".", "ZCalClkInfo_p2_bits"};
      this.ZCalClkInfo_p2.configure(this, null, "");
      this.ZCalClkInfo_p2.build();
      this.default_map.add_reg(this.ZCalClkInfo_p2, `UVM_REG_ADDR_WIDTH'h4, "RW", 0);
		this.ZCalClkInfo_p2_ZCalDfiClkTicksPer1uS = this.ZCalClkInfo_p2.ZCalDfiClkTicksPer1uS;
		this.ZCalDfiClkTicksPer1uS = this.ZCalClkInfo_p2.ZCalDfiClkTicksPer1uS;
      this.PUBReservedP1_p2 = ral_reg_DWC_DDRPHYA_ZCAL0_p2_PUBReservedP1_p2::type_id::create("PUBReservedP1_p2",,get_full_name());
      if(this.PUBReservedP1_p2.has_coverage(UVM_CVR_ALL))
      	this.PUBReservedP1_p2.cg_bits.option.name = {get_name(), ".", "PUBReservedP1_p2_bits"};
      this.PUBReservedP1_p2.configure(this, null, "");
      this.PUBReservedP1_p2.build();
      this.default_map.add_reg(this.PUBReservedP1_p2, `UVM_REG_ADDR_WIDTH'hFF, "RW", 0);
		this.PUBReservedP1_p2_PUBReservedP1_p2 = this.PUBReservedP1_p2.PUBReservedP1_p2;
      this.ZCalStopClk_p2 = ral_reg_DWC_DDRPHYA_ZCAL0_p2_ZCalStopClk_p2::type_id::create("ZCalStopClk_p2",,get_full_name());
      if(this.ZCalStopClk_p2.has_coverage(UVM_CVR_ALL))
      	this.ZCalStopClk_p2.cg_bits.option.name = {get_name(), ".", "ZCalStopClk_p2_bits"};
      this.ZCalStopClk_p2.configure(this, null, "");
      this.ZCalStopClk_p2.build();
      this.default_map.add_reg(this.ZCalStopClk_p2, `UVM_REG_ADDR_WIDTH'h32F, "RW", 0);
		this.ZCalStopClk_p2_ZCalStopClk_p2 = this.ZCalStopClk_p2.ZCalStopClk_p2;
   endfunction : build

	`uvm_object_utils(ral_block_DWC_DDRPHYA_ZCAL0_p2)


function void sample(uvm_reg_addr_t offset,
                     bit            is_read,
                     uvm_reg_map    map);
  if (get_coverage(UVM_CVR_ADDR_MAP)) begin
    m_offset = offset;
    cg_addr.sample();
  end
endfunction
endclass : ral_block_DWC_DDRPHYA_ZCAL0_p2


endpackage
`endif
