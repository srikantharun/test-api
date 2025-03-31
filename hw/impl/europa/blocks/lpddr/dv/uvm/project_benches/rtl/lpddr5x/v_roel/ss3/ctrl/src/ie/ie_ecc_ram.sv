//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ie/ie_ecc_ram.sv#3 $
// ------------------------------------------------------------------------------
// 
// Copyright 2024 Synopsys, INC.
// 
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
//            Inclusivity and Diversity" (Refer to article 000036315 at
//                        https://solvnetplus.synopsys.com)
// 
// Component Name   : DWC_ddrctl_lpddr54
// Component Version: 1.60a-lca00
// Release Type     : LCA
// Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
// ------------------------------------------------------------------------------

// ----------------------------------------------------------------------------
//                              DDR Controller
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//                              Description
//
// ----------------------------------------------------------------------------

`include "DWC_ddrctl_all_defs.svh"
module ie_ecc_ram
#(
    parameter WIDTH      = 64
   ,parameter MASK_WIDTH = 8
   ,parameter DEPTH      = 32
   ,parameter ADDR_BITS  = 5
   ,parameter OCPAR_EN   = 0
   ,parameter OCECC_EN   = 0
   ,parameter RD_CLR     = 0      //1: the mask will be clear after read. 0: no clear after read.
   ,parameter DUAL_RD    = 0      //1: dual read port; 0: single read port
   ,parameter FLS_EN     = 0      //1: enable flush interface to flush a block of mask. 0: not use flush interface, tie flush if to 0.
   ,parameter FLS_BLK_BITS= 2    //indicate address bits for one block size to flush
   ,parameter REGOUT     = 1'b0   //1: rdata valid in the next cycle of raddr, like RAM;
                                  //0: rdata valid in the same cycle with raddr, like ROM;
   ,parameter MASK_USED = 1       //1: rdata_mask_n/rdata_mask_n_2 are   used signals
                                  //0: rdata_mask_n/rdata_mask_n_2 are unused signals
   ,parameter OCCAP_EN = 0        //1: protection added o mask generating flops - pgen/pchk
                                  //0: No protection on mask generation
   ,parameter OCCAP_PIPELINE_EN = 0 //1: Extra cycle of pipeline on pchk output
                                    //0: No pipeline 

)
(  
    input                    clk       
   ,input                    rstn  
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in generate block       
   ,input                    wr        
   ,input  [MASK_WIDTH-1:0]  wdata_mask_n
   ,input  [ADDR_BITS-1:0]   waddr     
   ,input                    rd    //if RD_CLR is 1, rd will clear the rdata_mask_n[raddr], if RD_CLR is 0, rd is useless.
   ,input  [ADDR_BITS-1:0]   raddr   
   ,input  [ADDR_BITS-1:0]   raddr_2   
   ,input                    flush_en    //if FLS_EN is 1, flush_en will flush a block of mask, 
                                         //raddr is start address, 2**FLS_BLK_BITS is size, if FLS_EN is 0, tie them to 0.
   ,input  [ADDR_BITS-FLS_BLK_BITS-1:0]   flush_addr
   ,input                    reg_ddrc_occap_en
   ,input                    reg_ddrc_occap_en_r   
//spyglass enable_block W240
   ,input  [WIDTH-1:0]       wdata     
   ,input  [MASK_WIDTH-1:0]  wdata_par
           
   ,output [WIDTH-1:0]       rdata     
   ,output [MASK_WIDTH-1:0]  rdata_mask_n
   ,output [MASK_WIDTH-1:0]  rdata_par
   ,output [WIDTH-1:0]       rdata_2     
   ,output [MASK_WIDTH-1:0]  rdata_mask_n_2
   ,output [MASK_WIDTH-1:0]  rdata_par_2
   ,output                   ddrc_occap_ieeccram_parity_err

);
localparam OCCAP_TOTAL_MASK_WIDTH_BASE = MASK_WIDTH*DEPTH; //  ecc_ram_mask_n
localparam OCCAP_TOTAL_MASK_WIDTH      = OCCAP_TOTAL_MASK_WIDTH_BASE //  ecc_ram_mask_n
                                         + ((REGOUT==1) ? MASK_WIDTH : 0) // r_rdata_mask_n
                                         + ((REGOUT==1 && DUAL_RD==1) ? MASK_WIDTH : 0); // r_rdata_mask_n_2

localparam OCCAP_SL_W = 8;
localparam OCCAP_PARW = (OCCAP_EN==1) ? ((OCCAP_TOTAL_MASK_WIDTH%OCCAP_SL_W>0) ? OCCAP_TOTAL_MASK_WIDTH/OCCAP_SL_W+1 : OCCAP_TOTAL_MASK_WIDTH/OCCAP_SL_W) : 0;

//------------------------------ LOCAL PARAMETERS ------------------------------------

reg [WIDTH-1:0]   ecc_ram        [0:DEPTH-1];
reg [MASK_WIDTH-1:0] ecc_ram_mask_n [0:DEPTH-1];
reg [MASK_WIDTH-1:0] ecc_ram_par [0:DEPTH-1];

reg  [WIDTH-1:0]   i_rdata;
wire [MASK_WIDTH-1:0] i_rdata_mask_n;
wire [MASK_WIDTH-1:0] i_rdata_par;

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(i * 8)' found in module 'ie_ecc_ram'
//SJ: This coding style is acceptable and there is no plan to change it.

//-----------------------------------------------------------
// Write Side
//-----------------------------------------------------------
integer j;
//spyglass disable_block W528
//SMD: A signal or variable is set but never read - ecc_ram_par
//SJ: Used in generate block
always @ (posedge clk or negedge rstn) begin
integer i;
   if(!rstn) begin
      for (i=0; i<DEPTH; i=i+1) begin
         ecc_ram[i] <= {WIDTH{1'b0}};
         ecc_ram_par[i] <= {MASK_WIDTH{1'b0}};
      end
   end else if(wr) begin
      for (i=0; i<MASK_WIDTH; i=i+1) begin
         if(wdata_mask_n[i]) begin
           for (j=0;j<DEPTH;j++) begin
               if($unsigned(j)==waddr[ADDR_BITS-1:0])begin     
                 ecc_ram[j][i*8+:8] <= wdata[i*8+:8];
                 ecc_ram_par[j][i] <= wdata_par[i];
               end
           end 
         end
      end
   end
end
//spyglass enable_block W528

reg [MASK_WIDTH-1:0] ecc_ram_mask_n_nxt [0:DEPTH-1];

generate
 if(MASK_USED==1) begin: MASK_USED_1
   if(RD_CLR==1) begin: RD_CLR_1
      always @ (*) begin
      integer i;
         for (i=0; i<DEPTH; i=i+1) begin
            ecc_ram_mask_n_nxt[i] = ecc_ram_mask_n[i];
            if(wr & waddr==i)
               ecc_ram_mask_n_nxt[i] = ecc_ram_mask_n[i] | wdata_mask_n;
            if(rd & raddr==i)  //read and write access the same address, the new mask will put to rdata_mask_n and clear the mask by read.
               ecc_ram_mask_n_nxt[i] = {MASK_WIDTH{1'b0}};
         end
      end

      always @ (posedge clk or negedge rstn) begin
      integer i;
         if(!rstn) begin
            for (i=0; i<DEPTH; i=i+1) begin
               ecc_ram_mask_n[i] <= {MASK_WIDTH{1'b0}};
            end
         end else begin
            for (i=0; i<DEPTH; i=i+1) begin
               ecc_ram_mask_n[i] <= ecc_ram_mask_n_nxt[i];
            end
         end
      end
   end else if(FLS_EN==1) begin: FLS_EN_1
      always @ (*) begin
      integer i;
         for (i=0; i<DEPTH; i=i+1) begin
            ecc_ram_mask_n_nxt[i] = ecc_ram_mask_n[i];
            if(wr && waddr==i)
               ecc_ram_mask_n_nxt[i] = ecc_ram_mask_n[i] | wdata_mask_n;
//            if(flush_en && (i>>FLS_BLK_BITS)==flush_addr)
            if(flush_en && i>={flush_addr, {FLS_BLK_BITS{1'b0}}} && i<={flush_addr, {FLS_BLK_BITS{1'b1}}})
               ecc_ram_mask_n_nxt[i] = {MASK_WIDTH{1'b0}};
         end
      end

      always @ (posedge clk or negedge rstn) begin
      integer i;
         if(!rstn) begin
            for (i=0; i<DEPTH; i=i+1) begin
               ecc_ram_mask_n[i] <= {MASK_WIDTH{1'b0}};
            end
         end else begin
            for (i=0; i<DEPTH; i=i+1) begin
               ecc_ram_mask_n[i] <= ecc_ram_mask_n_nxt[i];
            end
         end
      end
   end else begin: RD_CLR_0
      always @ (posedge clk or negedge rstn) begin
      integer i;
         if(!rstn) begin
            for (i=0; i<DEPTH; i=i+1) begin
               ecc_ram_mask_n[i] <= {MASK_WIDTH{1'b0}};
            end
         end else if(wr) begin
         
           for (j=0;j<DEPTH;j++) begin
                   if($unsigned(j)==waddr[ADDR_BITS-1:0]) 
                     ecc_ram_mask_n[j] <= ecc_ram_mask_n[j] | wdata_mask_n;
                   end
//            ecc_ram_mask_n[waddr] <= ecc_ram_mask_n[waddr] | wdata_mask_n;
         end
      end
   end
 end

endgenerate
//-----------------------------------------------------------
// Read Side
//-----------------------------------------------------------


always @ (*) begin
integer i;
   i_rdata={WIDTH{1'b0}};
   if(wr && (waddr==raddr)) begin
      for (i=0; i<MASK_WIDTH; i=i+1) begin
         if(wdata_mask_n[i])
            i_rdata[i*8+:8] = wdata[i*8+:8];
         else begin
           for (j=0;j<DEPTH;j++) begin
           if($unsigned(j)==raddr[ADDR_BITS-1:0])
           i_rdata[i*8+:8] = ecc_ram[j][i*8+:8];
           end
       end
      end
   end else begin
           for (j=0;j<DEPTH;j++) begin
           if($unsigned(j)==raddr[ADDR_BITS-1:0]) 
              i_rdata = ecc_ram[j];
           end
   end
end

generate
   if (MASK_USED==1) begin: MASK_USED_en
      reg [MASK_WIDTH-1:0] i_rdata_mask_n_d;
      reg [MASK_WIDTH-1:0] ecc_ram_mask_n_tmp2;
      always @ (*) begin
       i_rdata_mask_n_d={MASK_WIDTH{1'b0}};
       ecc_ram_mask_n_tmp2={MASK_WIDTH{1'b0}};
         if(wr && (waddr==raddr)) begin
           for (j=0;j<DEPTH;j++) begin
                   if($unsigned(j)==waddr[ADDR_BITS-1:0]) begin
                   ecc_ram_mask_n_tmp2 = ecc_ram_mask_n[j] ;
                   end
           end
                   i_rdata_mask_n_d = ecc_ram_mask_n_tmp2 | wdata_mask_n;
         end else begin
           for (j=0;j<DEPTH;j++) begin
           if($unsigned(j)==raddr[ADDR_BITS-1:0]) 
              i_rdata_mask_n_d = ecc_ram_mask_n[j];
           end
         end
      end
      assign i_rdata_mask_n = i_rdata_mask_n_d;

   end
   else begin: MASK_USED_dis
      
      assign i_rdata_mask_n = {MASK_WIDTH{1'b0}};

   end
endgenerate

generate
   if (OCPAR_EN==1 || OCECC_EN==1) begin: OC_PAR_OR_ECC_en_rd
      reg [MASK_WIDTH-1:0] i_rdata_par_d;

      always @ (*) begin
      integer i;
         i_rdata_par_d={MASK_WIDTH{1'b0}};
         if(wr && (waddr==raddr)) begin
            for (i=0; i<MASK_WIDTH; i=i+1) begin
               if(wdata_mask_n[i])
                  i_rdata_par_d[i] = wdata_par[i];
               else begin
                      for (j=0;j<DEPTH;j++) begin
                      if($unsigned(j)==raddr[ADDR_BITS-1:0])
                      i_rdata_par_d[i] = ecc_ram_par[j][i];
                      end
                   end
            end
         end else begin
                      for (j=0;j<DEPTH;j++) begin
                      if($unsigned(j)==raddr[ADDR_BITS-1:0])
                      i_rdata_par_d = ecc_ram_par[j];
                      end
         end
      end

      assign i_rdata_par = i_rdata_par_d;

   end
   else begin: OC_PAR_OR_ECC_dis_rd
      
      assign i_rdata_par = {MASK_WIDTH{1'b0}};

   end
endgenerate


// select Register out or not
generate
   if(REGOUT==1) begin : REG_OUT_1
      reg [WIDTH-1:0]   r_rdata;
      reg [MASK_WIDTH-1:0] r_rdata_mask_n;
      reg [MASK_WIDTH-1:0] r_rdata_par;

      always @ (posedge clk or negedge rstn) begin
         if(!rstn) begin
            r_rdata        <= {WIDTH{1'b0}};
            r_rdata_mask_n <= {MASK_WIDTH{1'b0}};
            r_rdata_par    <= {MASK_WIDTH{1'b0}};
         end else begin
            r_rdata        <= i_rdata;
            r_rdata_mask_n <= i_rdata_mask_n;
            r_rdata_par    <= i_rdata_par;
         end
      end

      assign rdata        = r_rdata;
      assign rdata_mask_n = r_rdata_mask_n;
      assign rdata_par    = r_rdata_par;
   end else begin : REG_OUT_0
      assign rdata        = i_rdata;
      assign rdata_mask_n = i_rdata_mask_n;
      assign rdata_par    = i_rdata_par;
   end
endgenerate


wire [MASK_WIDTH-1:0] i_rdata_mask_n_2;

// generate read port 2
generate 
   if(DUAL_RD) begin : DUAL_RD_1
      reg [WIDTH-1:0]   i_rdata_2;
      wire [MASK_WIDTH-1:0] i_rdata_par_2;

      always @ (*) begin
      integer i;
      i_rdata_2={WIDTH{1'b0}};
         if(wr && (waddr==raddr_2)) begin
            for (i=0; i<MASK_WIDTH; i=i+1) begin
               if(wdata_mask_n[i])
                  i_rdata_2[i*8+:8] = wdata[i*8+:8];
               else begin
                    for (j=0;j<DEPTH;j++) begin
                    if($unsigned(j)==raddr_2[ADDR_BITS-1:0]) 
                       i_rdata_2[i*8+:8] = ecc_ram[j][i*8+:8];
                    end
               end
            end
         end else begin
                    for (j=0;j<DEPTH;j++) begin
                    if($unsigned(j)==raddr_2[ADDR_BITS-1:0]) 
                       i_rdata_2 = ecc_ram[j];
                    end
         end
      end  //always

        if (MASK_USED==1) begin: MASK_USED_en_2
          reg [MASK_WIDTH-1:0] i_rdata_mask_n_2_d;
          reg [MASK_WIDTH-1:0] ecc_ram_mask_n_tmp1;

          always @ (*) begin
          i_rdata_mask_n_2_d={MASK_WIDTH{1'b0}};
          ecc_ram_mask_n_tmp1={MASK_WIDTH{1'b0}};
            if(wr && (waddr==raddr_2)) begin
                    for (j=0;j<DEPTH;j++) begin
                    if($unsigned(j)==waddr[ADDR_BITS-1:0]) 
                    ecc_ram_mask_n_tmp1 = ecc_ram_mask_n[j] ;
                    end
                    i_rdata_mask_n_2_d = ecc_ram_mask_n_tmp1 | wdata_mask_n;
            end else begin
                     for (j=0;j<DEPTH;j++) begin
                    if($unsigned(j)==raddr_2[ADDR_BITS-1:0]) 
                      i_rdata_mask_n_2_d = ecc_ram_mask_n[j];
                    end
            end
          end

          assign  i_rdata_mask_n_2 = i_rdata_mask_n_2_d;
       end
       else begin: MASK_USED_dis_2
      
          assign  i_rdata_mask_n_2 = {MASK_WIDTH{1'b0}};

      end

      if (OCPAR_EN==1 || OCECC_EN==1) begin: OC_PAR_OR_ECC_en_2
         reg [MASK_WIDTH-1:0] i_rdata_par_2_d;

         always @ (*) begin
         integer i;
            i_rdata_par_2_d={MASK_WIDTH{1'b0}};
            if(wr && (waddr==raddr_2)) begin
               for (i=0; i<MASK_WIDTH; i=i+1) begin
                  if(wdata_mask_n[i])
                     i_rdata_par_2_d[i] = wdata_par[i];
                  else begin
                        for (j=0;j<DEPTH;j++) begin
                        if($unsigned(j)==raddr_2[ADDR_BITS-1:0]) 
                        i_rdata_par_2_d[i] = ecc_ram_par[j][i];
                        end
                       end
               end
            end else begin
                     for (j=0;j<DEPTH;j++) begin
                     if($unsigned(j)==raddr_2[ADDR_BITS-1:0]) 
                     i_rdata_par_2_d = ecc_ram_par[j];
                     end
            end
         end  //always

         assign i_rdata_par_2 = i_rdata_par_2_d;
      end
      else begin: OC_PAR_OR_ECC_dis_2

         assign i_rdata_par_2 = {MASK_WIDTH{1'b0}};

      end

      // select Register out or not
      if(REGOUT==1) begin : REG_OUT_1_DUAL_RD_1
         reg [WIDTH-1:0]   r_rdata_2;
         reg [MASK_WIDTH-1:0] r_rdata_mask_n_2;
         reg [MASK_WIDTH-1:0] r_rdata_par_2;

         always @ (posedge clk or negedge rstn) begin
            if(!rstn) begin
               r_rdata_2        <= {WIDTH{1'b0}};
               r_rdata_mask_n_2 <= {MASK_WIDTH{1'b0}};
               r_rdata_par_2    <= {MASK_WIDTH{1'b0}};
            end else begin
               r_rdata_2        <= i_rdata_2;
               r_rdata_mask_n_2 <= i_rdata_mask_n_2;
               r_rdata_par_2    <= i_rdata_par_2;
            end
         end

         assign rdata_2        = r_rdata_2;
         assign rdata_mask_n_2 = r_rdata_mask_n_2;
         assign rdata_par_2    = r_rdata_par_2;
      end else begin : REG_OUT_0_DUAL_RD_1
         assign rdata_2        = i_rdata_2;
         assign rdata_mask_n_2 = i_rdata_mask_n_2;
         assign rdata_par_2    = i_rdata_par_2;
      end
   end else begin : DUAL_RD_0
      assign rdata_2           = {WIDTH{1'b0}};
      assign rdata_mask_n_2    = {MASK_WIDTH{1'b0}};
      assign rdata_par_2       = {MASK_WIDTH{1'b0}};
   end
endgenerate


//spyglass enable_block SelfDeterminedExpr-ML

// generate based OCCAP_EN
// protects all "mask" related flip flops with per-byte parity
// These are:
// ecc_ram_mask_n - DEPTH*_MASK_WIDTH - Always
// rdata_mask_n   - MASK_WIDTH        - ONLY if REGOUT=1  
// rdata_mask_n_2 - MASK_WIDTH        - ONLY if REGOUT=1  && DUAL_RD=1
generate 
   if(OCCAP_EN) begin : OCCAP_en
      if (MASK_USED==1) begin : MASK_USED_1_DUAL_RD_1

        wire [OCCAP_PARW-1:0] parity_dummy, mask_in;

        wire [OCCAP_PARW-1:0] pgen_in_par, parity_err;
        wire [OCCAP_PARW-1:0] pgen_parity_corr_unused, pcheck_parity_corr_unused;
        
        reg [OCCAP_PARW-1:0]pgen_in_par_r;

        //wire pgen_en, pcheck_en;

        assign parity_dummy  = {OCCAP_PARW{1'b1}};
        assign mask_in       = {OCCAP_PARW{1'b1}};

        reg [OCCAP_TOTAL_MASK_WIDTH-1:0] pgen_ecc_ram_mask_n_nxt_w;
        reg [OCCAP_TOTAL_MASK_WIDTH-1:0] pchk_ecc_ram_mask_n_w;

        // re-wiring of 2d array into a single bus
        integer depth_count;
        always @(*) begin 

          for (depth_count=0; depth_count<DEPTH; depth_count=depth_count+1) begin
            pgen_ecc_ram_mask_n_nxt_w[depth_count*MASK_WIDTH+:MASK_WIDTH] = ecc_ram_mask_n_nxt[depth_count];
                pchk_ecc_ram_mask_n_w[depth_count*MASK_WIDTH+:MASK_WIDTH] = ecc_ram_mask_n[depth_count];
          end
        end

        // append i_rdata_mask_n/rdata_mask_n to top of bus if rdata_mask_n is used
        if (REGOUT==1) begin : REGOUT_1
          always @(*) begin
            pgen_ecc_ram_mask_n_nxt_w[             (OCCAP_TOTAL_MASK_WIDTH_BASE)+:MASK_WIDTH] = i_rdata_mask_n;
                pchk_ecc_ram_mask_n_w[             (OCCAP_TOTAL_MASK_WIDTH_BASE)+:MASK_WIDTH] = rdata_mask_n;
          end
        end

        // append i_rdata_mask_n_2/rdata_mask_n_2 to top of bus if rdata_mask_n_2 is used
        if (REGOUT==1 && DUAL_RD==1) begin : REGOUT_1_DUAL_RD_1
          always @(*) begin
              pgen_ecc_ram_mask_n_nxt_w[(OCCAP_TOTAL_MASK_WIDTH_BASE+MASK_WIDTH)+:MASK_WIDTH] = i_rdata_mask_n_2;
                pchk_ecc_ram_mask_n_w[             (OCCAP_TOTAL_MASK_WIDTH_BASE)+:MASK_WIDTH] = rdata_mask_n_2;
          end
        end

        // pgen
        DWC_ddr_umctl2_ocpar_calc
        
         #(
            .DW      (OCCAP_TOTAL_MASK_WIDTH), 
            .CALC    (1), // parity calc
            .PAR_DW  (OCCAP_PARW),
            .SL_W    (OCCAP_SL_W)
         )
         U_pgen
         (
            .data_in       (pgen_ecc_ram_mask_n_nxt_w),
            .parity_en     (reg_ddrc_occap_en),
            .parity_type   (1'b0),
            .parity_in     (parity_dummy),
            .mask_in       (mask_in),
            .parity_out    (pgen_in_par), // parity out
            .parity_corr   (pgen_parity_corr_unused) // not used
         );



         always @ (posedge clk or negedge rstn)
           if (~rstn) begin
             pgen_in_par_r <= {OCCAP_PARW{1'b0}};
           end else begin
             pgen_in_par_r <= pgen_in_par;
           end



         // pcheck
         DWC_ddr_umctl2_ocpar_calc
         
         #(
            .DW      (OCCAP_TOTAL_MASK_WIDTH),
            .CALC    (0), // parity check
            .PAR_DW  (OCCAP_PARW),
            .SL_W    (OCCAP_SL_W)
         )
         U_pcheck
         (
            .data_in       (pchk_ecc_ram_mask_n_w),
            .parity_en     (reg_ddrc_occap_en_r),
            .parity_type   (1'b0),
            .parity_in     (pgen_in_par_r), // parity in
            .mask_in       (mask_in),
            .parity_out    (parity_err), // parity error
            .parity_corr   (pcheck_parity_corr_unused) // not used
         );

              
         // error flag
         if (OCCAP_PIPELINE_EN==1) begin : OCCAP_PIPELINE_EN_1

           reg ddrc_occap_ieeccram_parity_err_r;
           always @ (posedge clk or negedge rstn) begin : ddrc_occap_ieeccram_parity_err_r_PROC
             if (~rstn) begin
               ddrc_occap_ieeccram_parity_err_r <= 1'b0;
             end else begin
               ddrc_occap_ieeccram_parity_err_r <= |parity_err;
             end
           end

           assign ddrc_occap_ieeccram_parity_err = ddrc_occap_ieeccram_parity_err_r;          

         end else begin : OCCAP_PIPELINE_EN_0
         
           assign ddrc_occap_ieeccram_parity_err = |parity_err; 

         end

      end else begin : MASK_USED_0
        assign ddrc_occap_ieeccram_parity_err = 1'b0; // drive output to 0 
      end
   
   end else begin : OCCAP_dis
     assign ddrc_occap_ieeccram_parity_err = 1'b0; // drive output to 0 
   end
endgenerate



endmodule
