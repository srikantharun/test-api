`ifndef AI_CORE_MVM_REF_MODEL_SV
`define AI_CORE_MVM_REF_MODEL_SV
`uvm_analysis_imp_decl(_axi4_lp_rcv_pkt)
`uvm_analysis_imp_decl(_axis_ifdw_rcv_pkt)
`uvm_analysis_imp_decl(_axis_ifd0_rcv_pkt)
`uvm_analysis_imp_decl(_axis_ifd2_rcv_pkt)
//typedef ai_core_mvm_subsys_reg_block MVM_RAL;
class ai_core_mvm_ref_model extends uvm_component;
  `uvm_component_utils(ai_core_mvm_ref_model)

  uvm_analysis_imp_axi4_lp_rcv_pkt #(svt_axi_transaction,ai_core_mvm_ref_model) axi4_lp_2_ref_model_export;
  uvm_analysis_imp_axis_ifdw_rcv_pkt #(svt_axi_transaction,ai_core_mvm_ref_model) axis_ifdw_2_ref_model_export;
  uvm_analysis_imp_axis_ifd0_rcv_pkt #(svt_axi_transaction,ai_core_mvm_ref_model) axis_ifd0_2_ref_model_export;
  uvm_analysis_imp_axis_ifd2_rcv_pkt #(svt_axi_transaction,ai_core_mvm_ref_model) axis_ifd2_2_ref_model_export;
   
  uvm_analysis_port #(svt_axi_transaction) ref_model_2_sb_expected_data_port;
  uvm_analysis_port #(token_agent_seq_item) ap_tok_out[VERIF_MVM_NUM_TOK_AGENTS]; //execution and program
  svt_axi_transaction axi_stream_expected_data_item;
  // QCMD memory
  bit [AXI_LT_DATA_WIDTH -1: 0] qcmd_mem [EXE_INSTR_DEPTH];
  // MVM memory

  typedef logic [7:0] 	mvm_mem_ifdw[IMC_ROWS][IMC_COLUMN];
  typedef logic [25:0] 	mvm_mem[IMC_ROWS][IMC_COLUMN];
  
  mvm_mem_ifdw mvm_mem_ifdw_0;
  mvm_mem_ifdw mvm_mem_ifdw_1;
  mvm_mem_ifdw mvm_mem_ifdw_2;
  mvm_mem_ifdw mvm_mem_ifdw_3;

  mvm_mem mvm_mem_0;
  mvm_mem mvm_mem_1;
  mvm_mem mvm_mem_2;
  mvm_mem mvm_mem_3;

  uvm_status_e status;

  mvm_prg_cmd_struct prg_q[$];
  mvm_exe_instr_struct qcmd;
  mvm_exe_cmd_header_struct exe_header;
  mvm_exe_cmd_struct exe_q[$];
  mvm_prg_swdp_cmd_struct prg_swdp[$];
  mvm_exe_swdp_cmd_struct exe_swdp[$];
  logic [IMC_COLUMN-1:0] [25:0] iau_out_matrix = {AXI_STREAM_IAU_DATA_WIDTH{1'b0}};
  logic [AXI_STREAM_IAU_DATA_WIDTH -1 : 0] iau_data;
  bit [63:0][0:25] iau_sign_extends_data;
  bit [63:0][0:25] sw_test_mode_signed_extend_data;

  svt_axi_transaction ifd0_xact_pkt[$];
  svt_axi_transaction ifd2_xact_pkt[$];
  int dp_ctrl;
  int column_cnt_iter;
  bit [AXI_STREAM_IAU_DATA_WIDTH -1 : 0] iau_data_srt[int];

  // mvm user Inteface Handle
  virtual mvm_if mvm_if;
    
  // AI Core MVM RAL Modl
  MVM_RAL mvm_regmodel;
  function new(string name ="", uvm_component parent = null);
    super.new(name,parent);
    axi4_lp_2_ref_model_export        = new("axi4_lp_2_ref_model_export", this);
    axis_ifdw_2_ref_model_export      = new("axis_ifdw_2_ref_model_export", this);
    axis_ifd0_2_ref_model_export      = new("axis_ifd0_2_ref_model_export", this);
    axis_ifd2_2_ref_model_export      = new("axis_ifd2_2_ref_model_export",this);
     
    ref_model_2_sb_expected_data_port = new("ref_model_2_sb_expected_data_port", this);
    /** create token analysis port */
    foreach (ap_tok_out[i]) begin
      ap_tok_out[i] = new($sformatf("ap_tok_out[%0d]", i),this);
    end
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Recieve mvm user interface handle
    uvm_config_db#(virtual mvm_if)::get(uvm_root::get(), "uvm_test_top", "mvm_if", mvm_if);
  endfunction : build_phase

  virtual function void write_axi4_lp_rcv_pkt(input svt_axi_transaction axi4_lp_pkt);
    uvm_report_info(get_type_name(), $psprintf("Ref model: received packet from AXI4 LP Report %s", axi4_lp_pkt.sprint()), UVM_HIGH);
    process_lp_packet(axi4_lp_pkt);
  endfunction : write_axi4_lp_rcv_pkt

  virtual function void write_axis_ifdw_rcv_pkt(input svt_axi_transaction axis_ifdw_pkt);
    uvm_report_info(get_type_name(), $psprintf("Ref model: received packet from AXIS IFDW Report %s", axis_ifdw_pkt.sprint()), UVM_HIGH);
     // fork join for the swdp cmd
     fork
       store_weight_set(axis_ifdw_pkt);
     join_none
  endfunction : write_axis_ifdw_rcv_pkt

  virtual function void write_axis_ifd0_rcv_pkt(input svt_axi_transaction axis_ifd0_pkt);
    uvm_report_info(get_type_name(), $psprintf("Ref model: received packet from AXIS IFD0 Report %s", axis_ifd0_pkt.sprint()), UVM_HIGH);
    ifd0_xact_pkt.push_back(axis_ifd0_pkt);
  endfunction : write_axis_ifd0_rcv_pkt

  virtual function void write_axis_ifd2_rcv_pkt(input svt_axi_transaction axis_ifd2_pkt);
    uvm_report_info(get_type_name(), $psprintf("Ref model: received packet from AXIS IFD2 Report %s", axis_ifd2_pkt.sprint()), UVM_HIGH);
    ifd2_xact_pkt.push_back(axis_ifd2_pkt);
  endfunction : write_axis_ifd2_rcv_pkt

  virtual function void process_lp_packet(input svt_axi_transaction axi4_lp_pkt);
    case (axi4_lp_pkt.addr) inside
      [MVMEXE_CSR_START_ADDR:MVMEXE_CSR_END_ADDR] :  process_exe_dp_ctrl(axi4_lp_pkt); //uvm_report_info(get_type_name(),"MVMEXE_CSR transaction",UVM_DEBUG);
      [MVMPRG_CSR_START_ADDR:MVMPRG_CSR_END_ADDR] : uvm_report_info(get_type_name(),"MVMPRG_CSR transaction",UVM_DEBUG);
      [MVM_EXE_CMDB_START_ADDR:MVM_EXE_CMDB_END_ADDR] : process_exe_cmdb(axi4_lp_pkt);
      [MVM_EXE_SWDP_CMDB_START_ADDR:MVM_EXE_SWDP_CMDB_END_ADDR] : uvm_report_info(get_type_name(),"MVM_EXE_SWDP_CMDB transaction",UVM_DEBUG);
      [MVM_EXE_INSTR_START_ADDR:MVM_EXE_INSTR_END_ADDR] : process_exe_instr(axi4_lp_pkt);
      [MVM_PRG_CMDB_START_ADDR:MVM_PRG_CMDB_END_ADDR] : process_prg_cmdb(axi4_lp_pkt);
      [MVM_PRG_SWDP_CMDB_START_ADDR:MVM_PRG_SWDP_CMDB_END_ADDR] : process_prg_swdp_cmdb(axi4_lp_pkt);
    endcase
    uvm_report_info(get_type_name(), $psprintf("Ref model: received packet from AXI4 LP Report process_lp_packet function %s", axi4_lp_pkt.sprint()), UVM_DEBUG);
  endfunction

  virtual function void process_prg_cmdb(input svt_axi_transaction axi4_lp_pkt);
    send_tok_cons(axi4_lp_pkt.data[0], VERIF_MVM_PRG_TOK_AGT);
    send_tok_prod(axi4_lp_pkt.data[0], VERIF_MVM_PRG_TOK_AGT);
    prg_q.push_back( axi4_lp_pkt.data[1]);
    uvm_report_info(get_type_name(), $psprintf("Ref model: Configured the MVM_PRG_CMDB = %p", prg_q), UVM_HIGH);
  endfunction

  virtual function void process_prg_swdp_cmdb(input svt_axi_transaction axi4_lp_pkt);
    prg_swdp.push_back(axi4_lp_pkt.data[0]);
    uvm_report_info(get_type_name(), $psprintf("Ref model: Configured the MVM_PRG_SWDPCMD = %p", prg_swdp), UVM_HIGH);
  endfunction

  virtual function void process_exe_dp_ctrl(input svt_axi_transaction axi4_lp_pkt);
    exe_swdp.push_back(axi4_lp_pkt.data[0]);
    uvm_report_info(get_type_name(), $psprintf("Ref model: Configured the MVM_EXE_DPCTRL = %p lp_pkt_data %h", exe_swdp, axi4_lp_pkt.data[0]), UVM_HIGH);
  endfunction 

  virtual function void process_exe_instr (input svt_axi_transaction axi4_lp_pkt);
    bit [7:0] qcmd_addr = ( (axi4_lp_pkt.addr - MVM_EXE_INSTR_START_ADDR) / 2);
    //flushing qcmnd before assigning
    qcmd = 0;
    uvm_report_info(get_type_name(), $psprintf("Ref model: Before Configuring the MVM_EXE_INSTR = %p,qcmd_addr=%0d", qcmd,qcmd_addr), UVM_HIGH);
    foreach (axi4_lp_pkt.data[i]) begin
      qcmd.a_s = axi4_lp_pkt.data[i][1:0];
      qcmd.a_u_pw = axi4_lp_pkt.data[i][5:2];
      qcmd.a_t_pw = axi4_lp_pkt.data[i][8:6];
      qcmd.wb_u_pw = axi4_lp_pkt.data[i][12:9];
      qcmd.wb_t_pw = axi4_lp_pkt.data[i][15:13];
      // Store the QCMD
      qcmd_mem[qcmd_addr+i] = qcmd;
      uvm_report_info(get_type_name(), $psprintf("Ref model: Configured the MVM_EXE_INSTR = %p,qcmd_addr=%0d", qcmd,qcmd_addr), UVM_HIGH);
      uvm_report_info(get_type_name(), $psprintf("Ref model: axi4_lp_pkt.data= %h",axi4_lp_pkt.data[i] ), UVM_HIGH);
      uvm_report_info(get_type_name(), $psprintf("Ref model: Configured the MVM_EXE_INSTR_mem = %p", qcmd_mem), UVM_HIGH);
    end
  endfunction

  virtual function void process_exe_cmdb (input svt_axi_transaction axi4_lp_pkt);
    foreach (axi4_lp_pkt.data[i]) begin
      if(i==0) begin
        exe_header = axi4_lp_pkt.data[i];
        send_tok_cons(axi4_lp_pkt.data[i], VERIF_MVM_EXE_TOK_AGT);
        send_tok_prod(axi4_lp_pkt.data[i], VERIF_MVM_EXE_TOK_AGT);
      end
      else begin
        exe_q.push_back(axi4_lp_pkt.data[i]);
        dp_ctrl = axi4_lp_pkt.data[i][63:56];
        if(dp_ctrl==1) begin
	        column_cnt_iter=2; 
	    end 
        else column_cnt_iter=1;
        
      end
    end
    uvm_report_info(get_type_name(), $psprintf("Ref model: Configured the EXE_HEADER = %p,MVM_EXE_CMDB[%0d] = %p", exe_header, exe_q.size-1,exe_q[exe_q.size-1]), UVM_HIGH);
    foreach (exe_q[i])
      uvm_report_info(get_type_name(), $psprintf("Ref model: MVM_EXE_CMDB[%0d] = %p", i, exe_q[i]), UVM_HIGH);
  endfunction

  virtual task store_weight_set (input svt_axi_transaction axis_ifdw_pkt);
    mvm_prg_cmd_struct prg = prg_q.pop_front();
    int ifdw_stream_length;
    int row_offset;
    int column_offset;
    int row_width ;
    int column_width ;
    int broadcast_mode ;
    int prg_iter ;
    byte ifdw_byte[64];
    integer len = -1;
    bit [1:0] weight_sets;
    bit [15:0] valid_offset;
    bit [2:0] prg_mode;
 
    begin
      row_offset = prg.a_u_pw * 64;
      column_offset = prg.a_t_pw * 64;
      row_width = (prg.wb_u_pw + 1) * 64;
      column_width = (prg.wb_t_pw + 1) * 64;
      broadcast_mode = prg.extra[3];
      // calculate the stream lenght
      ifdw_stream_length =  row_width * (prg.wb_t_pw + 1);
      weight_sets = prg.a_s;
      prg_iter = broadcast_mode ? 2 : 1;
      `uvm_info(get_type_name(), $psprintf("value of prg_iter is %d and broadcast_mode is %d",prg_iter,broadcast_mode), UVM_MEDIUM);
      prg_mode    = prg.extra[2:0];
    end
    `uvm_info(get_type_name(), $psprintf("getting inside store wet set "), UVM_MEDIUM);
     
    // check the stream lenght
    if ( $test$plusargs("IRQ_testing_so_no_data_checks") ) //TODO IRQ no data check
      `uvm_info("REF_NO_CHECK","no ref model checks", UVM_HIGH)
    else if(axis_ifdw_pkt.tdata.size() != ifdw_stream_length) begin
      `uvm_error(get_type_name, "Programming or IFDW length is not proper")
    end
    // Store to weight into memory
    if(prg_mode == 1) begin 
	  uvm_report_info(get_type_name(), $psprintf("PRG MODE 1 Ref model: store_weight_set row_width is %d column width is %d IMC_COLUMN is %d",row_width,column_width,IMC_COLUMN), UVM_DEBUG);
	  for(int column = column_offset; column < (column_offset + column_width); column=column+64) begin
	    for (int row = row_offset; row < (row_offset + row_width); row++) begin   	      
	      for(int sub_column = 0; sub_column < 64; sub_column++) begin  
	        if(sub_column == 0 ) begin
	          len++;  
	          uvm_report_info(get_type_name(), $psprintf("PRG MODE 1 Ref model: store_weight_set sub column is %d axis_ifdw_pkt[%0d][%0d][%0d]=%0h",sub_column,row,column,len,axis_ifdw_pkt.tdata[len]), UVM_DEBUG);
	          for(int shift=0;shift<64;shift++) begin
	            ifdw_byte[shift] = axis_ifdw_pkt.tdata[len] >> 8*shift;
	          end
	        end
	        uvm_report_info(get_type_name(), $psprintf("PRG MODE 1 Ref model: store_weight_set sub column is %d row is %d column is %d len is %d",sub_column,row,column,len), UVM_DEBUG);
	   
	        case (weight_sets)
	          0: mvm_mem_ifdw_0[row][column+sub_column] = ifdw_byte[sub_column%64];
	          1: mvm_mem_ifdw_1[row][column+sub_column] = ifdw_byte[sub_column%64];
	          2: mvm_mem_ifdw_2[row][column+sub_column] = ifdw_byte[sub_column%64];
	          3: mvm_mem_ifdw_3[row][column+sub_column] = ifdw_byte[sub_column%64];
	        endcase // case (weight_sets)
	        if(broadcast_mode == 1 )begin
	           case (weight_sets)   
	             0: begin 
	            mvm_mem_ifdw_0[row][column+sub_column+256] = ifdw_byte[sub_column%64];
	             end		      
	             1: mvm_mem_ifdw_1[row][column+sub_column+256] = ifdw_byte[sub_column%64];
	             2: mvm_mem_ifdw_2[row][column+sub_column+256] = ifdw_byte[sub_column%64];
	             3: mvm_mem_ifdw_3[row][column+sub_column+256] = ifdw_byte[sub_column%64];
	           endcase // case (weight_sets)
	        end		 		 
	        // For debug purpose : UVM_VERBOSITY = UVM_DEBUG
	        case (weight_sets)
	          0: uvm_report_info(get_type_name(), $psprintf("Ref model: store_weight_set mvm_mem_ifdw_0[%0d][%0d]=%0h",row,column+sub_column,mvm_mem_ifdw_0[row][column+sub_column]), UVM_DEBUG);
	          1: uvm_report_info(get_type_name(), $psprintf("Ref model: store_weight_set mvm_mem_ifdw_1[%0d][%0d]=%0h",row,column+sub_column,mvm_mem_ifdw_1[row][column+sub_column]), UVM_DEBUG);
	          2: uvm_report_info(get_type_name(), $psprintf("Ref model: store_weight_set mvm_mem_ifdw_2[%0d][%0d]=%0h",row,column+sub_column,mvm_mem_ifdw_2[row][column+sub_column]), UVM_DEBUG);
	          3: uvm_report_info(get_type_name(), $psprintf("Ref model: store_weight_set mvm_mem_ifdw_3[%0d][%0d]=%0h",row,column+sub_column,mvm_mem_ifdw_3[row][column+sub_column]), UVM_DEBUG);
	        endcase
	      end // for (int sub_column = 0; sub_column < 64; sub_column++)	      
	    end // for (int row = row_offset; row < (row_offset + row_width); row++)	   
	  end // for (int column = column_offset; column < (column_offset + column_width); column=column+64)	
     end else if(prg_mode == 2) begin // if (prg_mode == 2)
		uvm_report_info(get_type_name(), $psprintf("PRG MODE 2 Ref model: store_weight_set row_width is %d column width is %d IMC_COLUMN is %d",row_width,column_width,IMC_COLUMN), UVM_HIGH);
	for(int row = row_offset; row < (row_offset+row_width); row = row+64) begin
	   for(int column = column_offset; column < (column_offset + column_width); column=column+64) begin
	      for (int sub_row = 0; sub_row < 64; sub_row++) begin   	      
		 for(int sub_column = 0; sub_column < 64; sub_column++) begin  
		    if(sub_column == 0 ) begin
		       len++;  
		       uvm_report_info(get_type_name(), $psprintf("PRG MODE 2 Ref model: store_weight_set sub column is %d axis_ifdw_pkt[%0d][%0d][%0d]=%0h",sub_column,row,column,len,axis_ifdw_pkt.tdata[len]), UVM_DEBUG);
		       for(int shift=0;shift<64;shift++) begin
			  ifdw_byte[shift] = axis_ifdw_pkt.tdata[len] >> 8*shift;
		       end
		    end
		    uvm_report_info(get_type_name(), $psprintf("PRG MODE 2 Ref model: store_weight_set sub column is %d sub row is %d row is %d column is %d len is %d",sub_column,sub_row, row,column,len), UVM_HIGH);
		    
		    case (weight_sets)
		      0: mvm_mem_ifdw_0[row+sub_row][column+sub_column] = ifdw_byte[sub_column];
		      1: mvm_mem_ifdw_1[row+sub_row][column+sub_column] = ifdw_byte[sub_column];
		      2: mvm_mem_ifdw_2[row+sub_row][column+sub_column] = ifdw_byte[sub_column];
		      3: mvm_mem_ifdw_3[row+sub_row][column+sub_column] = ifdw_byte[sub_column];
		    endcase // case (weight_sets)
		    if(broadcast_mode == 1 )begin
		       case (weight_sets)   
			 0: mvm_mem_ifdw_0[row+sub_row][column+sub_column+256] = ifdw_byte[sub_column];
			 1: mvm_mem_ifdw_1[row+sub_row][column+sub_column+256] = ifdw_byte[sub_column];
			 2: mvm_mem_ifdw_2[row+sub_row][column+sub_column+256] = ifdw_byte[sub_column];
			 3: mvm_mem_ifdw_3[row+sub_row][column+sub_column+256] = ifdw_byte[sub_column];
		       endcase // case (weight_sets)
		    end		 		 
		    // For debug purpose : UVM_VERBOSITY = UVM_DEBUG
		    case (weight_sets)
		      0: uvm_report_info(get_type_name(), $psprintf("Ref model: store_weight_set mvm_mem_ifdw_0[%0d][%0d]=%0h",row+sub_row,column+sub_column+256,mvm_mem_ifdw_0[row+sub_row][column+sub_column]), UVM_DEBUG);
		      1: uvm_report_info(get_type_name(), $psprintf("Ref model: store_weight_set mvm_mem_ifdw_1[%0d][%0d]=%0h",row+sub_row,column+sub_column+256,mvm_mem_ifdw_1[row+sub_row][column+sub_column]), UVM_DEBUG);
		      2: uvm_report_info(get_type_name(), $psprintf("Ref model: store_weight_set mvm_mem_ifdw_2[%0d][%0d]=%0h",row+sub_row,column+sub_column+256,mvm_mem_ifdw_2[row+sub_row][column+sub_column]), UVM_DEBUG);
		      3: uvm_report_info(get_type_name(), $psprintf("Ref model: store_weight_set mvm_mem_ifdw_3[%0d][%0d]=%0h",row+sub_row,column+sub_column+256,mvm_mem_ifdw_3[row+sub_row][column+sub_column]), UVM_DEBUG);
		    endcase
		 end // for (int sub_column = 0; sub_column < 64; sub_column++)	      
	      end // for (int row = row_offset; row < (row_offset + row_width); row++)	   
	   end // for (int column = column_offset; column < (column_offset + column_width); column=column+64)
	end // for (int row = row_offset; row < (row_offset+row_width); row = row+64)	
     end else begin
	for (int row = row_offset; row < (row_offset + row_width); row++) begin
	   for(int column = column_offset; column < (column_offset + column_width); column++) begin
              if(column % 64 == 0) begin
		 len++;
		 uvm_report_info(get_type_name(), $psprintf("Ref model: store_weight_set axis_ifdw_pkt[%0d][%0d][%0d]=%0h",row,column,len,axis_ifdw_pkt.tdata[len]), UVM_DEBUG);
		 for(int shift=0;shift<64;shift++) begin
		    ifdw_byte[shift] = axis_ifdw_pkt.tdata[len] >> 8*shift;
		 end
              end
              case (weight_sets)
		0: mvm_mem_ifdw_0[row][column] = ifdw_byte[column%64];
		1: mvm_mem_ifdw_1[row][column] = ifdw_byte[column%64];
		2: mvm_mem_ifdw_2[row][column] = ifdw_byte[column%64];
		3: mvm_mem_ifdw_3[row][column] = ifdw_byte[column%64];
              endcase // case (weight_sets)
	      if(broadcast_mode==1) begin
		 case (weight_sets)
	      	   0: mvm_mem_ifdw_0[row][column+256] = ifdw_byte[column%64];
		   1: mvm_mem_ifdw_1[row][column+256] = ifdw_byte[column%64];
		   2: mvm_mem_ifdw_2[row][column+256] = ifdw_byte[column%64];
		   3: mvm_mem_ifdw_3[row][column+256] = ifdw_byte[column%64];
		 endcase // case (weight_sets)
	      end
	     		 	      	      
              // For debug purpose : UVM_VERBOSITY = UVM_DEBUG
              case (weight_sets)
		0: uvm_report_info(get_type_name(), $psprintf("Ref model: store_weight_set mvm_mem_ifdw_0[%0d][%0d]=%0h",row,column,mvm_mem_ifdw_0[row][column]), UVM_DEBUG);
		1: uvm_report_info(get_type_name(), $psprintf("Ref model: store_weight_set mvm_mem_ifdw_1[%0d][%0d]=%0h",row,column,mvm_mem_ifdw_1[row][column]), UVM_DEBUG);
		2: uvm_report_info(get_type_name(), $psprintf("Ref model: store_weight_set mvm_mem_ifdw_2[%0d][%0d]=%0h",row,column,mvm_mem_ifdw_2[row][column]), UVM_DEBUG);
		3: uvm_report_info(get_type_name(), $psprintf("Ref model: store_weight_set mvm_mem_ifdw_3[%0d][%0d]=%0h",row,column,mvm_mem_ifdw_3[row][column]), UVM_DEBUG);
              endcase
	   end // for (int column = column_offset; column < (column_offset + column_width); column++)	   
	end // for (int row = row_offset; row < (row_offset + row_width); row++)
     end // else: !if(prg_mode == 2)    
  endtask // store_weight_set
   
   
  virtual function void multiplication (input svt_axi_transaction axis_ifd0_pkt, input svt_axi_transaction axis_ifd2_pkt);
    mvm_exe_cmd_header_struct exe_h = exe_header;
    mvm_exe_cmd_struct exe = exe_q.pop_front();
    //mvm_exe_cmd_struct exe = exe_q[0];
    //int exe_swdp_enable = (mvm_regmodel.m_mvmexe_regmod.swdp_ctrl.exec_en.get() & mvm_regmodel.m_mvmexe_regmod.swdp_ctrl.sw_byp_en.get());
    int ifd0_2_stream_length;
    int iau_stream_length;
    int input_size;
    int output_size;
    int row_offset ;
    int column_offset;
    int column_adj;
    int row_width ;
    int column_width;
    byte ifd0_byte[64];
    int len ;
    bit ifdw_signed;
    bit ifd0_2_signed;
    integer iau_len = -1;
    int sw_imc_test_mode =(mvm_regmodel.m_mvmexe_regmod.dp_ctrl.imc_test_mode.get() && 'h7);
    bit[2:0] imc_test_mode = mvm_regmodel.m_mvmexe_regmod.dp_ctrl.imc_test_mode.get();
    int iau_data_trk=0;
    ifdw_signed = mvm_regmodel.m_mvmprg_regmod.dp_ctrl.signed_weights.get();
    ifd0_2_signed = mvm_regmodel.m_mvmexe_regmod.dp_ctrl.signed_inputs.get();
    axi_stream_expected_data_item     = svt_axi_transaction::type_id::create("axi_stream_expected_data_item");
    uvm_report_info(get_type_name(), $psprintf("Ref model: received packet in mulitipliation api is %s", axis_ifd0_pkt.sprint()), UVM_HIGH);
    uvm_report_info(get_type_name(), $psprintf("Ref model: multiplication ifdw_signed=%0d,ifd0_2_signed=%0d,exe=%0p sw_imc_test_mode is %d imc_test_mode %d",ifdw_signed,ifd0_2_signed,exe,sw_imc_test_mode,imc_test_mode), UVM_HIGH);
    // opcode shifted to hearder so change the below code when ref model enable 
    if(exe_h.cmd_format == 9) begin //bypass signed extention
      // calculate the stream lenght
      axi_stream_expected_data_item.tdata = new[axis_ifd0_pkt.tdata.size];
      uvm_report_info(get_type_name(), $psprintf("Ref model:multiplication exe.loop_iter=%0d, input_size =%0d,ifd0_2_stream_length=%0d,tdata.size=%0d",exe.loop_iter,input_size,ifd0_2_stream_length,axis_ifd0_pkt.tdata.size()), UVM_HIGH);
      foreach(axi_stream_expected_data_item.tdata[len]) begin
        for(int shift=0;shift<64;shift++) begin
          if(dp_ctrl> 0) begin
	        ifd0_byte[shift] = axis_ifd2_pkt.tdata[len] >> 8*shift; 
	      end else begin
	        ifd0_byte[shift] = axis_ifd0_pkt.tdata[len] >> 8*shift;
	      end 

        end
        for(int i=0;i<64;i++) begin
          iau_sign_extends_data[i] ={{19{ifd0_byte[i][7]}},ifd0_byte[i][6:0]};
        end
        axi_stream_expected_data_item.tdata[len]=iau_sign_extends_data;
        uvm_report_info(get_type_name(), $psprintf("Ref model: multiplication iau_sign_extends_data=%0h",iau_sign_extends_data), UVM_DEBUG);
      end
      // Send packet to
      ref_model_2_sb_expected_data_port.write(axi_stream_expected_data_item);
    end
    else begin // normal access without bypass
      for (int i=0; i < exe.loop_len; ++i) begin
        qcmd = qcmd_mem[exe.loop_ptr + i];
        input_size = input_size + (qcmd.wb_u_pw+1);
        output_size = output_size + (qcmd.wb_t_pw+1);
      end
      if(dp_ctrl==1) begin
        axi_stream_expected_data_item.tdata = new[output_size*exe.loop_iter*2];
        `uvm_info(get_type_name(), $psprintf("expected data packet size is %0d and dp_ctrl is %0d",axi_stream_expected_data_item.tdata.size(),dp_ctrl), UVM_HIGH);
      end else begin
        axi_stream_expected_data_item.tdata = new[output_size*exe.loop_iter];
        `uvm_info(get_type_name(), $psprintf("expected data packet size is %0d and dp_ctrl is %0d",axi_stream_expected_data_item.tdata.size(),dp_ctrl), UVM_HIGH);
      end
      for(int iteration = 1; iteration < exe.loop_iter + 1;iteration++) begin
        for (int loop_len_idx=0; loop_len_idx < exe.loop_len; ++loop_len_idx) begin
          uvm_report_info(get_type_name(), $psprintf("value of loop_len_idx related to loop_len is %d ",loop_len_idx), UVM_HIGH);
          qcmd = qcmd_mem[exe.loop_ptr + loop_len_idx];
          uvm_report_info(get_type_name(), $psprintf("Ref model: multiplication using MVM_EXE_INSTR = %p,qcmd_addr=%0d", qcmd, (exe.loop_ptr+loop_len_idx)), UVM_HIGH);
          input_size=0;
          output_size=0;
          input_size = input_size + (qcmd.wb_u_pw+1);
          output_size = output_size + (qcmd.wb_t_pw+1);
          row_offset = qcmd.a_u_pw * 64;
          column_offset = qcmd.a_t_pw*64;
          row_width = (qcmd.wb_u_pw +1) * 64;
          column_width = (qcmd.wb_t_pw + 1) * 64;
          uvm_report_info(get_type_name(), $psprintf("Ref model:multiplication input_size=%0d, row_off is %0d, col_off is %0d, row_len is %0d and col_len is %0d",input_size, row_offset, column_offset, row_width, column_width ), UVM_HIGH);
          uvm_report_info(get_type_name(), $psprintf("Ref model: number of iteration=%0d",iteration), UVM_HIGH);
          for (int col_cnt = 0 ; col_cnt<column_cnt_iter; col_cnt++) begin
            if(col_cnt==1) column_offset = 256 + column_offset;
            else column_offset = qcmd.a_t_pw*64;
            for(int column = column_offset; column < column_offset + column_width; column++) begin
              if(dp_ctrl > 0) begin
                len=(iteration-1) * (qcmd.wb_u_pw+1);
                `uvm_info(get_type_name(), $psprintf("dibw len is %0d and dp_ctrl is %0d",len,dp_ctrl), UVM_HIGH);		  
              end else begin
                len= ((iteration-1)*exe.loop_len + loop_len_idx) * (qcmd.wb_u_pw+1);
                `uvm_info(get_type_name(), $psprintf("len is %0d and dp_ctrl is %0d",len,dp_ctrl), UVM_HIGH);
              end
	          
              for (int row = row_offset; row < (row_offset + row_width); row++) begin
                if(row % 64 == 0) begin
                  for(int shift=0;shift<64;shift++) begin
                    //if(column >= column_offset + column_width) begin
                    if(column >= 256 && dp_ctrl==1) begin
                      ifd0_byte[shift] = axis_ifd2_pkt.tdata[len] >> 8*shift;
                    end
                    else if(dp_ctrl==3 && loop_len_idx==0) begin
                      ifd0_byte[shift] = axis_ifd0_pkt.tdata[len] >> 8*shift;
                    end
                    else if(dp_ctrl==3 && loop_len_idx==1) begin
                      ifd0_byte[shift] = axis_ifd2_pkt.tdata[len] >> 8*shift;
                    end
                    else begin
                      ifd0_byte[shift] = axis_ifd0_pkt.tdata[len] >> 8*shift;
                    end 
                    uvm_report_info(get_type_name(), $psprintf("Ref model: multiplication ifd0_byte[%0d]=%0h",shift,ifd0_byte[shift]), UVM_DEBUG);
                  end
                  // For debug purpose : UVM_VERBOSITY = UVM_DEBUG
                  uvm_report_info(get_type_name(), $psprintf("Ref model: multiplication axis_ifd0_pkt[%0d]=%0h ",len,axis_ifd0_pkt.tdata[len]), UVM_HIGH);
                  len++;
                end
                case (qcmd.a_s)
                  0: uvm_report_info(get_type_name(), $psprintf("Ref model: multiplication before mvm_mem_0[%0d][%0d]=%0h",row,column,mvm_mem_0[row][column]), UVM_DEBUG);
                  1: uvm_report_info(get_type_name(), $psprintf("Ref model: multiplication before mvm_mem_1[%0d][%0d]=%0h",row,column,mvm_mem_1[row][column]), UVM_DEBUG);
                  2: uvm_report_info(get_type_name(), $psprintf("Ref model: multiplication before mvm_mem_2[%0d][%0d]=%0h",row,column,mvm_mem_2[row][column]), UVM_DEBUG);
                  3: uvm_report_info(get_type_name(), $psprintf("Ref model: multiplication before mvm_mem_3[%0d][%0d]=%0h",row,column,mvm_mem_3[row][column]), UVM_DEBUG);
                endcase
                uvm_report_info(get_type_name(), $psprintf("Ref model: multiplication before ifd0_byte[%0d]=%0h,qcmd=%0p",(row%64),ifd0_byte[row%64],qcmd), UVM_DEBUG);
                case ({ifdw_signed, ifd0_2_signed ,qcmd.a_s})
                  4'b0000  : mvm_mem_0[row][column] = (mvm_mem_ifdw_0[row][column]) * ifd0_byte[row%64] ;
                  4'b0001  : mvm_mem_1[row][column] = (mvm_mem_ifdw_1[row][column]) * ifd0_byte[row%64] ;
                  4'b0010  : mvm_mem_2[row][column] = (mvm_mem_ifdw_2[row][column]) * ifd0_byte[row%64] ;
                  4'b0011  : mvm_mem_3[row][column] = (mvm_mem_ifdw_3[row][column]) * ifd0_byte[row%64] ;

                  4'b0100  : mvm_mem_0[row][column] = (mvm_mem_ifdw_0[row][column]) * { {18{ifd0_byte[row%64][7]}}, ifd0_byte[row%64][6:0] };
                  4'b0101  : mvm_mem_1[row][column] = (mvm_mem_ifdw_1[row][column]) * { {18{ifd0_byte[row%64][7]}}, ifd0_byte[row%64][6:0] };
                  4'b0110  : mvm_mem_2[row][column] = (mvm_mem_ifdw_2[row][column]) * { {18{ifd0_byte[row%64][7]}}, ifd0_byte[row%64][6:0] };
                  4'b0111  : mvm_mem_3[row][column] = (mvm_mem_ifdw_3[row][column]) * { {18{ifd0_byte[row%64][7]}}, ifd0_byte[row%64][6:0] };

                  4'b1000  : mvm_mem_0[row][column] = { {18{mvm_mem_ifdw_0[row][column][7]}}, mvm_mem_ifdw_0[row][column][6:0] } * ifd0_byte[row%64] ;
                  4'b1001  : mvm_mem_1[row][column] = { {18{mvm_mem_ifdw_0[row][column][7]}}, mvm_mem_ifdw_0[row][column][6:0] } * ifd0_byte[row%64] ;
                  4'b1010  : mvm_mem_2[row][column] = { {18{mvm_mem_ifdw_0[row][column][7]}}, mvm_mem_ifdw_0[row][column][6:0] } * ifd0_byte[row%64] ;
                  4'b1011  : mvm_mem_3[row][column] = { {18{mvm_mem_ifdw_0[row][column][7]}}, mvm_mem_ifdw_0[row][column][6:0] } * ifd0_byte[row%64] ;

                  4'b1100  : mvm_mem_0[row][column] =  $signed((mvm_mem_ifdw_0[row][column])) * $signed(ifd0_byte[row%64]);
                  4'b1101  : mvm_mem_1[row][column] =  $signed((mvm_mem_ifdw_1[row][column])) * $signed(ifd0_byte[row%64]);
                  4'b1110  : mvm_mem_2[row][column] =  $signed((mvm_mem_ifdw_2[row][column])) * $signed(ifd0_byte[row%64]);
                  4'b1111  : mvm_mem_3[row][column] =  $signed((mvm_mem_ifdw_3[row][column])) * $signed(ifd0_byte[row%64]);
                endcase
                // For debug purpose : UVM_VERBOSITY = UVM_DEBUG
                case (qcmd.a_s)
                  0: uvm_report_info(get_type_name(), $psprintf("Ref model: multiplication after mvm_mem_0[%0d][%0d]=%0h",row,column,mvm_mem_0[row][column]), UVM_DEBUG);
                  1: uvm_report_info(get_type_name(), $psprintf("Ref model: multiplication after mvm_mem_1[%0d][%0d]=%0h",row,column,mvm_mem_1[row][column]), UVM_DEBUG);
                  2: uvm_report_info(get_type_name(), $psprintf("Ref model: multiplication after mvm_mem_2[%0d][%0d]=%0h",row,column,mvm_mem_2[row][column]), UVM_DEBUG);
                  3: uvm_report_info(get_type_name(), $psprintf("Ref model: multiplication after mvm_mem_3[%0d][%0d]=%0h",row,column,mvm_mem_3[row][column]), UVM_DEBUG);
                endcase
              end
            end
          end
          //IAU data calculation
          column_offset = qcmd.a_t_pw*64;
          for (int col_cnt = 0 ; col_cnt<column_cnt_iter; col_cnt++) begin
            if(col_cnt==1) column_offset = 256 + column_offset;
            for (int column = column_offset; column <(column_offset+column_width); column++) begin
              for (int row = row_offset; row <(row_offset + row_width); row++) begin
                // For debug purpose : UVM_VERBOSITY = UVM_DEBUG
                case (qcmd.a_s)
                  0: uvm_report_info(get_type_name(), $psprintf("Ref model: iau_data addition before mvm_mem_0[%0d][%0d]=%0h",row,column,mvm_mem_0[row][column]), UVM_DEBUG);
                  1: uvm_report_info(get_type_name(), $psprintf("Ref model: iau_data addition before mvm_mem_1[%0d][%0d]=%0h",row,column,mvm_mem_1[row][column]), UVM_DEBUG);
                  2: uvm_report_info(get_type_name(), $psprintf("Ref model: iau_data addition before mvm_mem_2[%0d][%0d]=%0h",row,column,mvm_mem_2[row][column]), UVM_DEBUG);
                  3: uvm_report_info(get_type_name(), $psprintf("Ref model: iau_data addition before mvm_mem_3[%0d][%0d]=%0h",row,column,mvm_mem_3[row][column]), UVM_DEBUG);
                endcase
                uvm_report_info(get_type_name(), $psprintf("Ref model: iau_data multiplication before iau_out_matrix[%0d]=%0h",column,iau_out_matrix[column]), UVM_DEBUG);
                case (qcmd.a_s)
                  0: iau_out_matrix[column] = iau_out_matrix[column] + mvm_mem_0[row][column];
                  1: iau_out_matrix[column] = iau_out_matrix[column] + mvm_mem_1[row][column];
                  2: iau_out_matrix[column] = iau_out_matrix[column] + mvm_mem_2[row][column];
                  3: iau_out_matrix[column] = iau_out_matrix[column] + mvm_mem_3[row][column];
                endcase
                // For debug purpose : UVM_VERBOSITY = UVM_DEBUG
                case (qcmd.a_s)
                  0: uvm_report_info(get_type_name(), $psprintf("Ref model: iau_data addition after mvm_mem_0[%0d][%0d]=%0h",row,column,mvm_mem_0[row][column]), UVM_DEBUG);
                  1: uvm_report_info(get_type_name(), $psprintf("Ref model: iau_data addition after mvm_mem_1[%0d][%0d]=%0h",row,column,mvm_mem_1[row][column]), UVM_DEBUG);
                  2: uvm_report_info(get_type_name(), $psprintf("Ref model: iau_data addition after mvm_mem_2[%0d][%0d]=%0h",row,column,mvm_mem_2[row][column]), UVM_DEBUG);
                  3: uvm_report_info(get_type_name(), $psprintf("Ref model: iau_data addition after mvm_mem_3[%0d][%0d]=%0h",row,column,mvm_mem_3[row][column]), UVM_DEBUG);
                endcase
                uvm_report_info(get_type_name(), $psprintf("Ref model: iau_data multiplication after iau_out_matrix[%0d]=%0h",column,iau_out_matrix[column]), UVM_DEBUG);
              end
            end
          end
          
          for (int col_cnt = 0 ; col_cnt<column_cnt_iter; col_cnt++) begin
            column_adj =  qcmd.a_t_pw;
            if(col_cnt==1) column_adj = 4 + qcmd.a_t_pw ;
            //for (int column = qcmd.a_t_pw; column < ( column + qcmd.wb_t_pw + 1); column++) begin
            for (int column = column_adj; column < ( column_adj + qcmd.wb_t_pw + 1); column++) begin
              uvm_report_info(get_type_name(), $sformatf("Ref model:SW IMC test mode %h before sign extended iau_data=[%0h] iau_out_matrix = [%0h] iau_len ",sw_imc_test_mode,iau_data,iau_out_matrix), UVM_HIGH);	  
              iau_data = iau_out_matrix >> AXI_STREAM_IAU_DATA_WIDTH * column;
              iau_len++;          
              
              if(imc_test_mode) begin	
                for(int i = 0; i< AXI_LT_DATA_WIDTH; i++) begin
                  uvm_report_info(get_type_name(), $psprintf("Ref model:SW IMC test mode %h before sign extended iau_data [%h] sw_test_mode_signed_extend_data [%h] ",sw_imc_test_mode,iau_data,sw_test_mode_signed_extend_data), UVM_DEBUG);		  
                  sw_test_mode_signed_extend_data[i] = {{19{iau_data[((26*i)+7)]}},iau_data[(i*26) +:7]};
                  uvm_report_info(get_type_name(), $psprintf("Ref model:sw_test_mode_signed_extend_data [%h]",sw_test_mode_signed_extend_data), UVM_DEBUG);
                end // for (int i = 0; i< 64; i++)
                uvm_report_info(get_type_name(), $psprintf("Ref model:SW IMC test mode %h after sign extended sw_test_mode_signed_extend_data [%h] iau_len %d",sw_imc_test_mode,sw_test_mode_signed_extend_data,iau_len), UVM_HIGH);
                axi_stream_expected_data_item.tdata[iau_len]=sw_test_mode_signed_extend_data;	
                uvm_report_info(get_type_name(), $psprintf("Ref model: axi_stream_expected_data_item.tdata %p",axi_stream_expected_data_item.tdata), UVM_DEBUG);
              end else begin
                axi_stream_expected_data_item.tdata[iau_len]=iau_data;	 
                uvm_report_info(get_type_name(), $psprintf("Ref model:iau_out_matrix=%0h,shift = [%0d],iau_data=[%0h] column is %d",iau_out_matrix, (AXI_STREAM_IAU_DATA_WIDTH * column),iau_data, column), UVM_DEBUG);
              end // else: !if(imc_test_mode)
	            uvm_report_info(get_type_name(), $psprintf("Ref model:iau_out_matrix=%0h,shift = [%0d],iau_data=[%0h] column is %d axi_stream_expected_data_item.tdata %p",iau_out_matrix, (AXI_STREAM_IAU_DATA_WIDTH * column),iau_data, column, axi_stream_expected_data_item.data), UVM_HIGH);

              iau_data_srt[column] = axi_stream_expected_data_item.tdata[iau_len];
              uvm_report_info(get_type_name(), $psprintf("size of associative array after assigning is = %0d and column value is %od", iau_data_srt.num(), column ), UVM_HIGH);
            end
          end
	               
          // reset the iau data
          iau_out_matrix = {AXI_STREAM_IAU_DATA_WIDTH{1'b0}};
          if(dp_ctrl==1) begin
            column_cnt_iter=2; 
          end
          else column_cnt_iter=1;
          
          // calculate the stream lenght
          if(dp_ctrl == 3 ) begin
            ifd0_2_stream_length =  exe.loop_iter * input_size * exe.loop_len/2;
          end else begin	      
            ifd0_2_stream_length =  exe.loop_iter * input_size * exe.loop_len;
            uvm_report_info(get_type_name(), $psprintf("Ref model:multiplication exe.loop_iter=%0d, input_size =%0d,ifd0_2_stream_length=%0d,and exe;loop_len is %0d",exe.loop_iter,input_size,ifd0_2_stream_length, exe.loop_len), UVM_HIGH);
          end
	   
          // check the stream length
          if ( $test$plusargs("IRQ_testing_so_no_data_checks") ) //TODO IRQ no data check
           `uvm_info("REF_NO_CHECK","no ref model checks", UVM_HIGH)
          else
          if( dp_ctrl==3 && (loop_len_idx%2==0)) begin // loop_len_idx=>loop_len
            if(axis_ifd0_pkt.tdata.size() != ifd0_2_stream_length) begin
              `uvm_error(get_type_name, $sformatf("Programming or IFD0 length is not proper from line 497 size %0d",  axis_ifd0_pkt.tdata.size()))
            end
          end
          else if ( dp_ctrl==3 && (loop_len_idx%2!=0)) begin // loop_len_idx=>loop_len
            if(axis_ifd2_pkt.tdata.size() != ifd0_2_stream_length) begin
               `uvm_error(get_type_name, $sformatf("Programming or IFD0 length is not proper from line 497 size is %d", axis_ifd0_pkt.tdata.size()))
            end
          end
          else begin
            if(axis_ifd0_pkt.tdata.size() != ifd0_2_stream_length) begin
              `uvm_error(get_type_name, $sformatf("Programming or IFD0 length is not proper from line 497 size is %d", axis_ifd0_pkt.tdata.size()))
            end
          end // else: !if( dp_ctrl==3 && (exe.loop_len%2!=0))
          if( dp_ctrl==3 && loop_len_idx%2==1 ) begin
            foreach (iau_data_srt[j]) begin
              axi_stream_expected_data_item.tdata[iau_data_trk] = iau_data_srt[j];
              uvm_report_info(get_type_name(), $psprintf(" after sorting value of iau_data_srt[j] = %0d and iau_data_trk is %0d and value in packet is %0h",iau_data_srt[j], iau_data_trk, axi_stream_expected_data_item.tdata[iau_data_trk] ), UVM_HIGH);
              iau_data_trk++;
            end
            // Empty the assoiative array before next iteration
            iau_data_srt.delete();
          end

        end  //len

      end    //Iteration
      
      // Send packet to
      ref_model_2_sb_expected_data_port.write(axi_stream_expected_data_item);
    end
  endfunction
  
  //function to send token information to the upper layers when active
  function void send_tok_cons(mvm_cmd_header_t p_header, mvm_tok_agt_type_t p_agt_type);
    token_agent_seq_item l_tok_item;

    //check into the data if the consumer token bit is active or not
    foreach (p_header.token_cons[i]) begin
      if(p_header.token_cons[i]==1) begin
        l_tok_item = token_agent_seq_item::type_id::create("l_tok_item", this);
        l_tok_item.m_tok_path_name = $sformatf("%s[%0d]", p_agt_type.name(), i);
        l_tok_item.m_type_enm = TOK_CONS_MON;
        //send to the scoreboard
        if(p_agt_type==VERIF_MVM_PRG_TOK_AGT) ap_tok_out[VERIF_MVM_PRG_TOK_AGT].write(l_tok_item);
        else                                  ap_tok_out[VERIF_MVM_EXE_TOK_AGT].write(l_tok_item);
      end
    end
  endfunction : send_tok_cons

  //function to send token information to the upper layers when active
  function void send_tok_prod(mvm_cmd_header_t p_header, mvm_tok_agt_type_t p_agt_type);
    token_agent_seq_item l_tok_item;

    foreach (p_header.token_prod[i]) begin
      if(p_header.token_prod[i]==1) begin
        l_tok_item = token_agent_seq_item::type_id::create("l_tok_item", this);
        l_tok_item.m_tok_path_name = $sformatf("%s[%0d]", p_agt_type.name(), i);
        l_tok_item.m_type_enm = TOK_PROD_MON;
        //send to the scoreboard
        if(p_agt_type==VERIF_MVM_PRG_TOK_AGT) ap_tok_out[VERIF_MVM_PRG_TOK_AGT].write(l_tok_item);
        else                                  ap_tok_out[VERIF_MVM_EXE_TOK_AGT].write(l_tok_item);
      end
    end
  endfunction : send_tok_prod


  task run_phase(uvm_phase phase);
    forever begin
      svt_axi_transaction axis_ifd0_pkt, axis_ifd2_pkt;
      //mvm_exe_cmd_struct exe = exe_q[0];
      `uvm_info(get_type_name(), $psprintf("getting inside run_phase "), UVM_MEDIUM);

      wait(ifd0_xact_pkt.size()>0);
      axis_ifd0_pkt = ifd0_xact_pkt[0]; 
      ifd0_xact_pkt.pop_front();
      //multiplication(axis_ifd0_pkt);
      `uvm_info(get_type_name(), $psprintf("value of dp_ctrl is %d ",dp_ctrl ), UVM_MEDIUM);
      if(dp_ctrl > 0) begin
        `uvm_info(get_type_name(), $psprintf("entered inside if part"), UVM_MEDIUM);
        wait(ifd2_xact_pkt.size()>0);
        axis_ifd2_pkt = ifd2_xact_pkt[0]; 
        ifd2_xact_pkt.pop_front();
        //multiplication(axis_ifd2_pkt);
      end
      multiplication(axis_ifd0_pkt,axis_ifd2_pkt);   
      `uvm_info(get_type_name(), $psprintf("multiplication with each ifd0 and ifd2"), UVM_MEDIUM);
    end 
  endtask:run_phase

endclass
`endif
