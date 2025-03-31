// Copyright (C) 2007, Andes Technology Corp. Confidential Proprietary
`timescale 1ps / 1ps
`include "config.inc"
`include "xmr.vh"

`ifndef NDS_IPIPE_TIMEOUT
    `define NDS_IPIPE_TIMEOUT 200000
`endif

module instn_simple_pipe_mon(
  input logic enable,
  input logic new_file
);


parameter XLEN					    = `NDS_XLEN;
parameter PALEN				    	    = `NDS_BIU_ADDR_WIDTH;
parameter VALEN				    	    = `NDS_VALEN;
parameter EXTVALEN			    	    = ((`NDS_MMU_SCHEME != "bare") && (XLEN > VALEN)) ? VALEN+1 : VALEN;
localparam FPIQ_SIZE			    	    = 8;
localparam FPIQ_PTR_BITS		    	    = $clog2(FPIQ_SIZE);
localparam FLEN				    	    = (`NDS_FPU_TYPE == "dp") ? 64 : 32;
localparam EXTFLEN			    	    = (FLEN > 0) ? FLEN : 1;
localparam RVN_SUPPORT			    	    = `NDS_RVN_SUPPORT;
localparam RVC_SUPPORT			    	    = `NDS_RVC_SUPPORT;
localparam RVV_SUPPORT			    	    = `NDS_RVV_SUPPORT;
localparam FPU_TYPE                         	    = `NDS_FPU_TYPE;
localparam ACE_SUPPORT                      	    = `NDS_ACE_SUPPORT;
localparam DSP_SUPPORT                      	    = `NDS_DSP_SUPPORT;
localparam NUM_PRIVILEGE_LEVELS             	    = `NDS_NUM_PRIVILEGE_LEVELS;
localparam PERFORMANCE_MONITOR              	    = `NDS_PERFORMANCE_MONITOR;
localparam STACKSAFE_SUPPORT                	    = `NDS_STACKSAFE_SUPPORT;
localparam DEBUG_SUPPORT                    	    = `NDS_DEBUG_SUPPORT;
localparam MAX_NUM_TRIGGER                  	    = 8;
localparam NUM_TRIGGER                      	    = `NDS_NUM_TRIGGER;
localparam ILM_SIZE_KB                      	    = `NDS_ILM_SIZE_KB;
localparam ILM_ECC_TYPE                     	    = `NDS_ILM_ECC_TYPE;
localparam DLM_SIZE_KB                      	    = `NDS_DLM_SIZE_KB;
localparam DLM_ECC_TYPE                     	    = `NDS_DLM_ECC_TYPE;
localparam ICACHE_SIZE_KB                   	    = `NDS_ICACHE_SIZE_KB;
localparam ICACHE_ECC_TYPE                  	    = `NDS_ICACHE_ECC_TYPE;
localparam DCACHE_SIZE_KB                   	    = `NDS_DCACHE_SIZE_KB;
localparam DCACHE_ECC_TYPE                  	    = `NDS_DCACHE_ECC_TYPE;
localparam WRITE_AROUND_SUPPORT             	    = `NDS_WRITE_AROUND_SUPPORT;
localparam SLAVE_PORT_SUPPORT		    	    = `NDS_SLAVE_PORT_SUPPORT;
localparam MMU_SCHEME                       	    = `NDS_MMU_SCHEME;
localparam PMP_ENTRIES                      	    = `NDS_PMP_ENTRIES;
localparam PMA_ENTRIES                      	    = `NDS_PMA_ENTRIES;
localparam LOCALINT_SLPECC                  	    = `NDS_LOCALINT_SLPECC;
localparam LOCALINT_SBE                     	    = `NDS_LOCALINT_SBE;
localparam LOCALINT_HPMINT                  	    = `NDS_LOCALINT_HPMINT;
localparam BIU_ADDR_WIDTH                   	    = `NDS_BIU_ADDR_WIDTH;
localparam BIU_DATA_WIDTH                   	    = `NDS_BIU_DATA_WIDTH;
localparam UNALIGNED_ACCESS                 	    = `NDS_UNALIGNED_ACCESS;
localparam VECTOR_PLIC_SUPPORT              	    = `NDS_VECTOR_PLIC_SUPPORT;
`ifdef NDS_ILM_BASE
localparam ILM_BASE                         	    = `NDS_ILM_BASE;
`else
localparam ILM_BASE                         	    = 64'h1000_0000;
`endif
`ifdef NDS_DLM_BASE
localparam DLM_BASE                         	    = `NDS_DLM_BASE;
`else
localparam DLM_BASE                         	    = 64'h2000_0000;
`endif

localparam CAUSE_LEN				    = 10;
localparam DCAUSE_LEN				    = 3;
localparam MESSAGE_LENGTH			    = 300;

`ifdef VPU_INST_DEBUG
localparam VPU_INST_DEBUG			    = 1;
`else
localparam VPU_INST_DEBUG			    = 0;
`endif
`ifdef NB_WB_TIME_DEBUG
localparam NB_WB_TIME				    = 1;
`else
localparam NB_WB_TIME				    = 0;
`endif

localparam  PC_MSB        = EXTVALEN-1;
localparam  ROB_SIZE      = 128;
localparam  SNAPSHOT_SIZE = 28;
localparam  IFREE_SIZE    = 96;
localparam  FFREE_SIZE    = 96;
localparam  ECAUSE_MSB    = 12;
localparam  ECC_MSB       = 12;
localparam  PID_MSB       = 5;
localparam  UOP_MSB       = 16;
localparam  BTAG_MSB      = 5;
localparam  OPAC_MSB      = 2;
localparam  RESUME_MSB    = 1;
localparam  BPQ_IDX_MSB   = 4;
localparam  MDHT_IDX_MSB  = 9;
localparam  CMT_AOP_MSB   = 7;
localparam  RAS_IDX_MSB   = 2;
localparam  LOOP_IDX_MSB  = 3;

localparam  IARF_SIZE     = 32;
localparam  FARF_SIZE     = 32;
localparam  IPRF_SIZE     = IARF_SIZE + IFREE_SIZE;
localparam  FPRF_SIZE     = FARF_SIZE + FFREE_SIZE;
localparam  ARF_IDX_MSB   = (FARF_SIZE > IARF_SIZE) ? ($clog2(FARF_SIZE)-1) : ($clog2(IARF_SIZE)-1);
localparam  PRF_IDX_MSB   = (FPRF_SIZE > IPRF_SIZE) ? ($clog2(FPRF_SIZE)-1) : ($clog2(IPRF_SIZE)-1);
localparam  IPRF_IDX_MSB  = $clog2(IPRF_SIZE)-1;
localparam  FPRF_IDX_MSB  = $clog2(FPRF_SIZE)-1;
localparam  AGE_MSB       = $clog2(ROB_SIZE);


`define IPIPE   `NDS_CORE.mk_ipipe
`define FPIPE   `NDS_CORE.mk_fpipe
`define IPRF    `NDS_CORE.mk_iprf
`define FPRF    `NDS_CORE.mk_fprf
`define GLUE    `NDS_CORE.mk_core_glue
`define ROB     `NDS_CORE.mk_rob
`define CMT     `NDS_CORE.mk_cmt
`define CSR     `NDS_CORE.mk_csr
`define IFU     `NDS_CORE.mk_ifu
`define DRU     `NDS_CORE.mk_dru

`ifndef TARGET_EMULATION
initial begin
        $timeformat(-9, 2, " ns");
end
`endif

int fp = 0;
string filename;
initial begin
`ifndef TARGET_EMULATION
  #0; //delay added because the sequence of events in questa is different from vcs. This is needed for questa.
`endif
  filename = $sformatf("./instruction_dump_ax65_id%0d.log", HART_ID);
end

bit new_file_prev = 0;

always @(posedge `NDS_CORE.core_clk) begin
  new_file_prev <= new_file;

  if (new_file && !new_file_prev) begin
    if (fp) begin
      $display("closing file %0s", filename);
      $fflush(fp);
      $fclose(fp);
    end
    $display("opening file %0s", filename);
    fp = $fopen(filename, "w");
  end
end

final begin
  $fclose(fp);
end

wire [8*5-1:0]   xreg_abi_names[31:0];
wire [8*5-1:0]   freg_abi_names[31:0];

assign xreg_abi_names[ 0] = "zero";
assign xreg_abi_names[ 1] = "ra";
assign xreg_abi_names[ 2] = "sp";
assign xreg_abi_names[ 3] = "gp";
assign xreg_abi_names[ 4] = "tp";
assign xreg_abi_names[ 5] = "t0";
assign xreg_abi_names[ 6] = "t1";
assign xreg_abi_names[ 7] = "t2";
assign xreg_abi_names[ 8] = "s0";
assign xreg_abi_names[ 9] = "s1";
assign xreg_abi_names[10] = "a0";
assign xreg_abi_names[11] = "a1";
assign xreg_abi_names[12] = "a2";
assign xreg_abi_names[13] = "a3";
assign xreg_abi_names[14] = "a4";
assign xreg_abi_names[15] = "a5";
assign xreg_abi_names[16] = "a6";
assign xreg_abi_names[17] = "a7";
assign xreg_abi_names[18] = "s2";
assign xreg_abi_names[19] = "s3";
assign xreg_abi_names[20] = "s4";
assign xreg_abi_names[21] = "s5";
assign xreg_abi_names[22] = "s6";
assign xreg_abi_names[23] = "s7";
assign xreg_abi_names[24] = "s8";
assign xreg_abi_names[25] = "s9";
assign xreg_abi_names[26] = "s10";
assign xreg_abi_names[27] = "s11";
assign xreg_abi_names[28] = "t3";
assign xreg_abi_names[29] = "t4";
assign xreg_abi_names[30] = "t5";
assign xreg_abi_names[31] = "t6";

assign freg_abi_names[ 0] = "ft0";
assign freg_abi_names[ 1] = "ft1";
assign freg_abi_names[ 2] = "ft2";
assign freg_abi_names[ 3] = "ft3";
assign freg_abi_names[ 4] = "ft4";
assign freg_abi_names[ 5] = "ft5";
assign freg_abi_names[ 6] = "ft6";
assign freg_abi_names[ 7] = "ft7";
assign freg_abi_names[ 8] = "fs0";
assign freg_abi_names[ 9] = "fs1";
assign freg_abi_names[10] = "fa0";
assign freg_abi_names[11] = "fa1";
assign freg_abi_names[12] = "fa2";
assign freg_abi_names[13] = "fa3";
assign freg_abi_names[14] = "fa4";
assign freg_abi_names[15] = "fa5";
assign freg_abi_names[16] = "fa6";
assign freg_abi_names[17] = "fa7";
assign freg_abi_names[18] = "fs2";
assign freg_abi_names[19] = "fs3";
assign freg_abi_names[20] = "fs4";
assign freg_abi_names[21] = "fs5";
assign freg_abi_names[22] = "fs6";
assign freg_abi_names[23] = "fs7";
assign freg_abi_names[24] = "fs8";
assign freg_abi_names[25] = "fs9";
assign freg_abi_names[26] = "fs10";
assign freg_abi_names[27] = "fs11";
assign freg_abi_names[28] = "ft8";
assign freg_abi_names[29] = "ft9";
assign freg_abi_names[30] = "ft10";
assign freg_abi_names[31] = "ft11";

wire      [63:0] HART_ID	= `NDS_CORE.hart_id;
wire             core_reset_n	= enable ? `NDS_CORE.core_reset_n : 0;
wire             core_clk    	= enable ? `NDS_CORE.core_clk : 0;
wire [VALEN-1:0] reset_vector	= enable ? `NDS_CORE.reset_vector : 0;


localparam IBUF_SIZE = 256;
localparam IBUF_DMSB = (PC_MSB + 1) + 32 - 1;
localparam IBUF_PMSB  = $clog2(IBUF_SIZE) - 1;

wire            decode0_taken      = `DRU.rq_w_taken0;
wire            decode1_taken      = `DRU.rq_w_taken1;
wire            decode2_taken      = `DRU.rq_w_taken2;
wire            decode3_taken      = `DRU.rq_w_taken3;

wire [PC_MSB:0] decode0_instr_pc   = `DRU.d1_instr0_pc;
wire [PC_MSB:0] decode1_instr_pc   = `DRU.d1_instr1_pc;
wire [PC_MSB:0] decode2_instr_pc   = `DRU.d1_instr2_pc;
wire [PC_MSB:0] decode3_instr_pc   = `DRU.d1_instr3_pc;
wire     [31:0] decode0_instr_data = `DRU.d1_instr0_data;
wire     [31:0] decode1_instr_data = `DRU.d1_instr1_data;
wire     [31:0] decode2_instr_data = `DRU.d1_instr2_data;
wire     [31:0] decode3_instr_data = `DRU.d1_instr3_data;

wire [PC_MSB:0] commit0_instr_pc   = {`CMT.trace0_pc_nx[VALEN-1], `CMT.trace0_pc_nx, 1'b0};
wire [PC_MSB:0] commit1_instr_pc   = {`CMT.trace1_pc_nx[VALEN-1], `CMT.trace1_pc_nx, 1'b0};
wire [PC_MSB:0] commit2_instr_pc   = {`CMT.trace2_pc_nx[VALEN-1], `CMT.trace2_pc_nx, 1'b0};
wire [PC_MSB:0] commit3_instr_pc   = {`CMT.trace3_pc_nx[VALEN-1], `CMT.trace3_pc_nx, 1'b0};
reg      [31:0] commit0_instr_data;
reg      [31:0] commit1_instr_data;
reg      [31:0] commit2_instr_data;
reg      [31:0] commit3_instr_data;

wire [IBUF_PMSB:0] ibuf_wptr_nx;
reg  [IBUF_PMSB:0] ibuf_wptr;
wire [IBUF_PMSB:0] ibuf_wptr0 = ibuf_wptr;
wire [IBUF_PMSB:0] ibuf_wptr1 = ibuf_wptr + {{(IBUF_PMSB-2){1'b0}}, 3'd1};
wire [IBUF_PMSB:0] ibuf_wptr2 = ibuf_wptr + {{(IBUF_PMSB-2){1'b0}}, 3'd2};
wire [IBUF_PMSB:0] ibuf_wptr3 = ibuf_wptr + {{(IBUF_PMSB-2){1'b0}}, 3'd3};

reg                ibuf_we  [0:IBUF_SIZE-1];
reg  [IBUF_DMSB:0] ibuf_nx  [0:IBUF_SIZE-1];
reg  [IBUF_DMSB:0] ibuf_reg [0:IBUF_SIZE-1];

assign ibuf_wptr_nx = decode3_taken ? ibuf_wptr + {{(IBUF_PMSB-2){1'b0}}, 3'd4} :
                      decode2_taken ? ibuf_wptr + {{(IBUF_PMSB-2){1'b0}}, 3'd3} :
                      decode1_taken ? ibuf_wptr + {{(IBUF_PMSB-2){1'b0}}, 3'd2} :
                      decode0_taken ? ibuf_wptr + {{(IBUF_PMSB-2){1'b0}}, 3'd1} :
		                      ibuf_wptr                               ;

always @(posedge core_clk or negedge core_reset_n) begin
	if (!core_reset_n)
		ibuf_wptr <= {(IBUF_PMSB+1){1'b0}};
	else
		ibuf_wptr <= ibuf_wptr_nx;
end

generate
genvar j;
for (j = 0; j < IBUF_SIZE; j = j + 1) begin: gen_ibuf_wr
	assign ibuf_we[j] = (decode0_taken & (ibuf_wptr0 == j[IBUF_PMSB:0]))
	                  | (decode1_taken & (ibuf_wptr1 == j[IBUF_PMSB:0]))
	                  | (decode2_taken & (ibuf_wptr2 == j[IBUF_PMSB:0]))
	                  | (decode3_taken & (ibuf_wptr3 == j[IBUF_PMSB:0]))
			  ;
	assign ibuf_nx[j] = (decode0_taken & (ibuf_wptr0 == j[IBUF_PMSB:0])) ? {decode0_instr_data, decode0_instr_pc} :
	                    (decode1_taken & (ibuf_wptr1 == j[IBUF_PMSB:0])) ? {decode1_instr_data, decode1_instr_pc} :
	                    (decode2_taken & (ibuf_wptr2 == j[IBUF_PMSB:0])) ? {decode2_instr_data, decode2_instr_pc} :
	                    (decode3_taken & (ibuf_wptr3 == j[IBUF_PMSB:0])) ? {decode3_instr_data, decode3_instr_pc} :
                            {(IBUF_DMSB+1){1'b0}};

	always @(posedge core_clk or negedge core_reset_n) begin
		if (!core_reset_n)
			ibuf_reg[j] <= {(IBUF_DMSB+1){1'b0}};
		else if (ibuf_we[j])
			ibuf_reg[j] <= ibuf_nx[j];
	end
end
endgenerate

always @* begin: gen_ibuf_rd
	integer k;

	commit0_instr_data = {(IBUF_DMSB+1){1'b0}};
	commit1_instr_data = {(IBUF_DMSB+1){1'b0}};
	commit2_instr_data = {(IBUF_DMSB+1){1'b0}};
	commit3_instr_data = {(IBUF_DMSB+1){1'b0}};

	for (k = 0; k < IBUF_SIZE; k = k + 1) begin
		commit0_instr_data = commit0_instr_data
		                   | ({32{(commit0_instr_pc == ibuf_reg[k][PC_MSB:0])}} & ibuf_reg[k][IBUF_DMSB:(PC_MSB+1)])
				   ;
		commit1_instr_data = commit1_instr_data
		                   | ({32{(commit1_instr_pc == ibuf_reg[k][PC_MSB:0])}} & ibuf_reg[k][IBUF_DMSB:(PC_MSB+1)])
				   ;
		commit2_instr_data = commit2_instr_data
		                   | ({32{(commit2_instr_pc == ibuf_reg[k][PC_MSB:0])}} & ibuf_reg[k][IBUF_DMSB:(PC_MSB+1)])
				   ;
		commit3_instr_data = commit3_instr_data
		                   | ({32{(commit3_instr_pc == ibuf_reg[k][PC_MSB:0])}} & ibuf_reg[k][IBUF_DMSB:(PC_MSB+1)])
				   ;
	end

	commit0_instr_data = {{16{(&commit0_instr_data[1:0])}}, 16'hffff} & commit0_instr_data;
	commit1_instr_data = {{16{(&commit1_instr_data[1:0])}}, 16'hffff} & commit1_instr_data;
	commit2_instr_data = {{16{(&commit2_instr_data[1:0])}}, 16'hffff} & commit2_instr_data;
	commit3_instr_data = {{16{(&commit3_instr_data[1:0])}}, 16'hffff} & commit3_instr_data;
end

reg  nseq_pc_check;
wire nseq_pc_check_set = `CMT.cmt_resume_flush_req
                       | `IPIPE.ipipe_mispred_flush_req
		       ;
wire nseq_pc_check_clr = decode0_taken;

always @(posedge core_clk or negedge core_reset_n) begin
	if (!core_reset_n)
		nseq_pc_check <= 1'b0;
	else if (nseq_pc_check_set)
		nseq_pc_check <= 1'b1;
	else if (nseq_pc_check_clr)
		nseq_pc_check <= 1'b0;
end

reg  [PC_MSB:0] nseq_pc_ref;
wire [PC_MSB:0] nseq_pc_ref_nx = `CMT.cmt_resume_flush_req ? {`CMT.cmt_ifu_resume_addr,   1'b0} :
                                                             {`IPIPE.ipipe_ifu_wb_target, 1'b0} ;

always @(posedge core_clk or negedge core_reset_n) begin
	if (!core_reset_n)
		nseq_pc_ref <= {(PC_MSB+1){1'b0}};
	else if (nseq_pc_check_set)
		nseq_pc_ref <= nseq_pc_ref_nx;
end

wire [PC_MSB:0] nseq_pc_hdl = `DRU.d1_instr0_pc;

always @(posedge core_clk) begin
	if (core_reset_n & nseq_pc_check & `DRU.d1_instr0_valid & (nseq_pc_ref !== nseq_pc_hdl)) begin
		$fwrite(fp, "---------------------------------------------\n");
		$fwrite(fp, "%0t:ipipe:ERROR: IFU returns wrong PC after receiving a resume/redirect fetch request\n", $time);
		$fwrite(fp, "%0t:ipipe:ERROR: ref PC (%016h)\n", $time, nseq_pc_ref);
		$fwrite(fp, "%0t:ipipe:ERROR: hdl PC (%016h)\n", $time, nseq_pc_hdl);
    $fflush(fp);
		$finish;
	end
end


wire [AGE_MSB:0] rob_read0_age = {`ROB.rob_oldest_age[AGE_MSB:2], 2'd0};
wire [AGE_MSB:0] rob_read1_age = {`ROB.rob_oldest_age[AGE_MSB:2], 2'd1};
wire [AGE_MSB:0] rob_read2_age = {`ROB.rob_oldest_age[AGE_MSB:2], 2'd2};
wire [AGE_MSB:0] rob_read3_age = {`ROB.rob_oldest_age[AGE_MSB:2], 2'd3};

wire       [3:0] commit0_dsel = `ROB.u_mk_remap_commit.dst_sel0;
wire       [3:0] commit1_dsel = `ROB.u_mk_remap_commit.dst_sel1;
wire       [3:0] commit2_dsel = `ROB.u_mk_remap_commit.dst_sel2;
wire       [3:0] commit3_dsel = `ROB.u_mk_remap_commit.dst_sel3;

wire [AGE_MSB:0] commit0_age  = ({(AGE_MSB+1){commit0_dsel[0]}} & rob_read0_age)
                              | ({(AGE_MSB+1){commit0_dsel[1]}} & rob_read1_age)
                              | ({(AGE_MSB+1){commit0_dsel[2]}} & rob_read2_age)
                              | ({(AGE_MSB+1){commit0_dsel[3]}} & rob_read3_age)
                              ;
wire [AGE_MSB:0] commit1_age  = ({(AGE_MSB+1){commit1_dsel[0]}} & rob_read0_age)
                              | ({(AGE_MSB+1){commit1_dsel[1]}} & rob_read1_age)
                              | ({(AGE_MSB+1){commit1_dsel[2]}} & rob_read2_age)
                              | ({(AGE_MSB+1){commit1_dsel[3]}} & rob_read3_age)
                              ;
wire [AGE_MSB:0] commit2_age  = ({(AGE_MSB+1){commit2_dsel[0]}} & rob_read0_age)
                              | ({(AGE_MSB+1){commit2_dsel[1]}} & rob_read1_age)
                              | ({(AGE_MSB+1){commit2_dsel[2]}} & rob_read2_age)
                              | ({(AGE_MSB+1){commit2_dsel[3]}} & rob_read3_age)
                              ;
wire [AGE_MSB:0] commit3_age  = ({(AGE_MSB+1){commit3_dsel[0]}} & rob_read0_age)
                              | ({(AGE_MSB+1){commit3_dsel[1]}} & rob_read1_age)
                              | ({(AGE_MSB+1){commit3_dsel[2]}} & rob_read2_age)
                              | ({(AGE_MSB+1){commit3_dsel[3]}} & rob_read3_age)
                              ;


localparam INUM_OF_BANK     = ((1 << (IPRF_IDX_MSB + 1)) > IPRF_SIZE) ? 3 : 2;
localparam IBANK_DFLT_SIZE  = (INUM_OF_BANK == 3) ? ((IPRF_SIZE - IARF_SIZE)/2) : (IPRF_SIZE/2);

localparam IBANK0_SIZE      = IBANK_DFLT_SIZE;
localparam IBANK1_SIZE      = IBANK_DFLT_SIZE;
localparam IBANK2_SIZE      = (INUM_OF_BANK == 3) ? IARF_SIZE : 0;

localparam IBANK0_MIN  = 0;
localparam IBANK0_MAX  = 0          + IBANK0_SIZE;
localparam IBANK1_MIN  = IBANK0_MAX;
localparam IBANK1_MAX  = IBANK0_MAX + IBANK1_SIZE;
localparam IBANK2_MIN  = IBANK1_MAX;
localparam IBANK2_MAX  = IBANK1_MAX + IBANK2_SIZE;

wire [XLEN-1:0] iprf_val [0:IPRF_SIZE-1];

generate
genvar m;
for (m = 0; m < IPRF_SIZE; m = m + 1) begin: gen_iprf_val
	if ((m >= IBANK0_MIN) && (m < IBANK0_MAX)) begin
		assign iprf_val[m] = `IPRF.gen_iprf_bank0_yes.u_mk_iprf_bank0.iprf_val[(m%IBANK0_SIZE)];
	end
	else if ((m >= IBANK1_MIN) && (m < IBANK1_MAX)) begin
		assign iprf_val[m] = `IPRF.gen_iprf_bank1_yes.u_mk_iprf_bank1.iprf_val[(m%IBANK1_SIZE)];
	end
	else if ((m >= IBANK2_MIN) && (m < IBANK2_MAX)) begin
		assign iprf_val[m] = `IPRF.gen_iprf_bank2_yes.u_mk_iprf_bank2.iprf_val[(m%IBANK2_SIZE)];
	end
	else begin
		assign iprf_val[m] = {XLEN{1'b0}};
	end
end
endgenerate

localparam FNUM_OF_BANK     = ((1 << (FPRF_IDX_MSB + 1)) > FPRF_SIZE) ? 3 : 2;
localparam FBANK_DFLT_SIZE  = (FNUM_OF_BANK == 3) ? ((FPRF_SIZE - FARF_SIZE)/2) : (FPRF_SIZE/2);

localparam FBANK0_SIZE      = FBANK_DFLT_SIZE;
localparam FBANK1_SIZE      = FBANK_DFLT_SIZE;
localparam FBANK2_SIZE      = (FNUM_OF_BANK == 3) ? FARF_SIZE : 0;

localparam FBANK0_MIN  = 0;
localparam FBANK0_MAX  = 0          + FBANK0_SIZE;
localparam FBANK1_MIN  = FBANK0_MAX;
localparam FBANK1_MAX  = FBANK0_MAX + FBANK1_SIZE;
localparam FBANK2_MIN  = FBANK1_MAX;
localparam FBANK2_MAX  = FBANK1_MAX + FBANK2_SIZE;

wire [FLEN-1:0] fprf_val [0:FPRF_SIZE-1];

generate
genvar n;
for (n = 0; n < FPRF_SIZE; n = n + 1) begin: gen_fprf_val
	if ((n >= FBANK0_MIN) && (n < FBANK0_MAX)) begin
		assign fprf_val[n] = `FPRF.gen_fprf_bank0_yes.u_mk_fprf_bank0.fprf_val[(n%FBANK0_SIZE)];
	end
	else if ((n >= FBANK1_MIN) && (n < FBANK1_MAX)) begin
		assign fprf_val[n] = `FPRF.gen_fprf_bank1_yes.u_mk_fprf_bank1.fprf_val[(n%FBANK1_SIZE)];
	end
	else if ((n >= FBANK2_MIN) && (n < FBANK2_MAX)) begin
		assign fprf_val[n] = `FPRF.gen_fprf_bank2_yes.u_mk_fprf_bank2.fprf_val[(n%FBANK2_SIZE)];
	end
	else begin
		assign fprf_val[n] = {FLEN{1'b0}};
	end
end
endgenerate


wire [XLEN-1:0] csr_xlen_wmask =
((`IPIPE.ipipe_csr_waddr >= 12'h3b0) && (`IPIPE.ipipe_csr_waddr <= 12'h3bf)) ? {{(XLEN-PALEN+2){1'b0}}, {(PALEN-2){1'b1}}} :
                                                                               {XLEN{1'b1}};


wire [31:0] mon_cmt_a_id = HART_ID[31:0];
wire [31:0] mon_cmt_0_id = HART_ID[31:0];
wire [31:0] mon_cmt_1_id = HART_ID[31:0];
wire [31:0] mon_cmt_2_id = HART_ID[31:0];
wire [31:0] mon_cmt_3_id = HART_ID[31:0];

reg normal_init = 1'b0;
reg dcrash_init = 1'b0;

always @(posedge core_clk or negedge core_reset_n) begin
      if (!core_reset_n) begin
        normal_init  <= 1'b0;
        dcrash_init  <= 1'b0;
      end
      else begin
        normal_init  <= `CMT.csr_init_event & ~`CMT.crash_debug_en;
        dcrash_init  <= `CMT.csr_init_event ? `CMT.crash_debug_en : (~`CMT.csr_halt_mode & dcrash_init);
      end
end

reg [31:0] cnt_no_dec = 32'd0;
reg [31:0] cnt_no_cmt = 32'd0;

bit core_wfi_mode_prev = 0;

always @(posedge core_clk) begin
      if (core_reset_n) begin
      	cnt_no_cmt   <= `ROB.rob_is_empty_r              ? 32'd0 :
      	                `ROB.rob_cmt_commit0_instr_valid ? 32'd0 :
      	                `ROB.rob_cmt_commit1_instr_valid ? 32'd0 :
      	                `ROB.rob_cmt_commit2_instr_valid ? 32'd0 :
      	                `ROB.rob_cmt_commit3_instr_valid ? 32'd0 :
      	                `CMT.core_wfi_mode               ? 32'd0 :
			                                   (cnt_no_cmt + 32'd1);

      	cnt_no_dec   <= `DRU.d1_instr0_valid             ? 32'd0 :
      	                `CMT.core_wfi_mode               ? 32'd0 :
			                                   (cnt_no_dec + 32'd1);
      end

      if (cnt_no_cmt >= `NDS_IPIPE_TIMEOUT) begin
              $fwrite(fp, "---------------------------------------------\n");
	      $fwrite(fp, "%0t:ipipe:ERROR:%0d cpu cycles passed without instruction retirement\n", $time, cnt_no_cmt);
        $fflush(fp);
    	      $finish;
      end

      if (cnt_no_dec >= `NDS_IPIPE_TIMEOUT) begin
              $fwrite(fp, "---------------------------------------------\n");
	      $fwrite(fp, "%0t:ipipe:ERROR:%0d cpu cycles passed without ready-to-decode instruction\n", $time, cnt_no_dec);
        $fflush(fp);
    	      $finish;
      end

      core_wfi_mode_prev <= `CMT.core_wfi_mode;
      if (`CMT.core_wfi_mode && (core_wfi_mode_prev == 0)) begin
              $fwrite(fp, "%0t:enter wfi mode\n", $time);
              $fflush(fp);
      end
      if (`CMT.cmt_resume_flush_req) begin
              $fwrite(fp, "%0t:resume:@%016h\n", $time, {`CMT.cmt_ifu_resume_addr, 1'b0});
              $fflush(fp);
      end

      if (`CMT.nmi_taken) begin
              $fwrite(fp, "%0t:%0s:%01d:nmi cause=%h\n", $time, "ipipe", mon_cmt_a_id, `CMT.trap_mcause[9:0]);
              $fflush(fp);
      end

      if (normal_init) begin
      	      $fwrite(fp, "%0t:%0s:%01d:reset %010h\n", $time, "ipipe", 0, reset_vector);
              $fflush(fp);
      end

      if (`CMT.cmt_csr_halt_en) begin
      	     if (dcrash_init) begin
	        $fwrite(fp, "%0t:%0s:%01d:reset %h debugmode\n", $time, "ipipe", mon_cmt_a_id, reset_vector);
                $fwrite(fp, "%0t:%0s:%01d:debug cause=%h\n", $time, "ipipe", mon_cmt_a_id, 3'd3);
                $fflush(fp);
	     end
	     else begin
             	$fwrite(fp, "%0t:%0s:%01d:debug cause=%h\n", $time, "ipipe", mon_cmt_a_id, `CMT.trap_dcsr_cause);
              $fflush(fp);
	     end
      end

      if (`CMT.a_commit_taken) begin
	      if (`CMT.except_taken) begin
        	      $fwrite(fp, "%0t:%0s:%01d:@%016h=%08h exception cause=%h\n", $time, "ipipe", mon_cmt_a_id,
		               commit0_instr_pc,
		               commit0_instr_data,
			       `CMT.trap_mcause[9:0]
			      );
          $fflush(fp);
	      end
	      else if (`CMT.retire0_csrw_en_nx) begin
        	      $fwrite(fp, "%0t:%0s:%01d:@%016h=%08h %4s=%016h csr%h=%h\n", $time, "ipipe", mon_cmt_a_id,
		               commit0_instr_pc,
		               commit0_instr_data,
		               (`ROB.rob_cmt_commit_abnormal_prd1_type ? freg_abi_names[`ROB.rob_cmt_commit_abnormal_ard1_idx] : xreg_abi_names[`ROB.rob_cmt_commit_abnormal_ard1_idx]),
		               (`ROB.rob_cmt_commit_abnormal_prd1_type ? fprf_val[`ROB.rob_cmt_commit_abnormal_prd1_idx] : iprf_val[`ROB.rob_cmt_commit_abnormal_prd1_idx]),
			       (`IPIPE.ipipe_csr_waddr),
			       (`IPIPE.ipipe_csr_wdata & csr_xlen_wmask)
			      );
          $fflush(fp);
	      end
	      else if (`CMT.retire0_valid_nx)begin
        	      $fwrite(fp, "%0t:%0s:%01d:@%016h=%08h %4s=%016h\n", $time, "ipipe", mon_cmt_a_id,
		               commit0_instr_pc,
		               commit0_instr_data,
		               (`ROB.rob_cmt_commit_abnormal_prd1_type ? freg_abi_names[`ROB.rob_cmt_commit_abnormal_ard1_idx] : xreg_abi_names[`ROB.rob_cmt_commit_abnormal_ard1_idx]),
		               (`ROB.rob_cmt_commit_abnormal_prd1_type ? fprf_val[`ROB.rob_cmt_commit_abnormal_prd1_idx] : iprf_val[`ROB.rob_cmt_commit_abnormal_prd1_idx])
			      );
          $fflush(fp);
	      end
      end
      if (`CMT.retire0_valid_nx & `CMT.n_commit0_taken) begin
              $fwrite(fp, "%0t:%0s:%01d:@%016h=%08h %4s=%016h\n", $time, "ipipe", mon_cmt_0_id,
	               commit0_instr_pc,
	               commit0_instr_data,
	               (`ROB.rob_cmt_commit0_instr_prd1_type ? freg_abi_names[`ROB.rob_cmt_commit0_instr_ard1_idx] : xreg_abi_names[`ROB.rob_cmt_commit0_instr_ard1_idx]),
	               (`ROB.rob_cmt_commit0_instr_prd1_type ? fprf_val[`ROB.rob_cmt_commit0_instr_prd1_idx] : iprf_val[`ROB.rob_cmt_commit0_instr_prd1_idx])
		      );
          $fflush(fp);
      end
      if (`CMT.retire1_valid_nx & `CMT.n_commit1_taken) begin
              $fwrite(fp, "%0t:%0s:%01d:@%016h=%08h %4s=%016h\n", $time, "ipipe", mon_cmt_1_id,
	               commit1_instr_pc,
	               commit1_instr_data,
	               (`ROB.rob_cmt_commit1_instr_prd1_type ? freg_abi_names[`ROB.rob_cmt_commit1_instr_ard1_idx] : xreg_abi_names[`ROB.rob_cmt_commit1_instr_ard1_idx]),
	               (`ROB.rob_cmt_commit1_instr_prd1_type ? fprf_val[`ROB.rob_cmt_commit1_instr_prd1_idx] : iprf_val[`ROB.rob_cmt_commit1_instr_prd1_idx])
		      );
          $fflush(fp);
      end
      if (`CMT.retire2_valid_nx & `CMT.n_commit2_taken) begin
              $fwrite(fp, "%0t:%0s:%01d:@%016h=%08h %4s=%016h\n", $time, "ipipe", mon_cmt_2_id,
	               commit2_instr_pc,
	               commit2_instr_data,
	               (`ROB.rob_cmt_commit2_instr_prd1_type ? freg_abi_names[`ROB.rob_cmt_commit2_instr_ard1_idx] : xreg_abi_names[`ROB.rob_cmt_commit2_instr_ard1_idx]),
	               (`ROB.rob_cmt_commit2_instr_prd1_type ? fprf_val[`ROB.rob_cmt_commit2_instr_prd1_idx] : iprf_val[`ROB.rob_cmt_commit2_instr_prd1_idx])
		      );
          $fflush(fp);
      end
      if (`CMT.retire3_valid_nx & `CMT.n_commit3_taken) begin
              $fwrite(fp, "%0t:%0s:%01d:@%016h=%08h %4s=%016h\n", $time, "ipipe", mon_cmt_3_id,
	               commit3_instr_pc,
	               commit3_instr_data,
	               (`ROB.rob_cmt_commit3_instr_prd1_type ? freg_abi_names[`ROB.rob_cmt_commit3_instr_ard1_idx] : xreg_abi_names[`ROB.rob_cmt_commit3_instr_ard1_idx]),
	               (`ROB.rob_cmt_commit3_instr_prd1_type ? fprf_val[`ROB.rob_cmt_commit3_instr_prd1_idx] : iprf_val[`ROB.rob_cmt_commit3_instr_prd1_idx])
		      );
          $fflush(fp);
      end
end


endmodule


