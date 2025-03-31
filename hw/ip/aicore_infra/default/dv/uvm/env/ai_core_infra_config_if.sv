
/**
 * Abstract:
 * Defines an interface that provides access to a reset signal.  This
 * interface can be used to write sequences to drive the reset logic.
 */

`ifndef GUARD_AI_CORE_INFRA_CONFIG_IF_SVI
`define GUARD_AI_CORE_INFRA_CONFIG_IF_SVI

 `define HP_SLV 2
 `define LP_SLV 6

interface ai_core_infra_config_if();
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import ai_core_infra_uvm_pkg::*;
  import ai_core_infra_ral_pkg::*;
  
  logic clk;

   logic [7:0] cid;
   logic [31:0] bid_scbd[`HP_SLV + `LP_SLV];
   logic dma_pkt=0;
   mstr_initiator_e mstr_initiator;
   slv_receiver_e slv_receiver;
   rd_intrlv_src_e rd_intrlv_src;
   reg_blk_e reg_blk;
   atu_cfg_e atu_cfg = 0;
   throttle_src_e throttle_src;
   throttle_mode_e throttle_mode;
   logic [1:0] dma_chnl;
   logic sys_ctrl_throttle = 0;
   real T = 25 ; // Signal to be forced by test bench, timing of when the force happens is controlled by test bench
   real V = 0.8; // Voltage to be forced by test bench for Voltage evaluation mode
   integer P = 0;
   logic DATA_VALID;
  
   logic hart_unavail_async_o;
   logic hart_unavail_async;
   logic ax25_clk_en_signal;
   logic disable_cdc_level_for_ai_core_obs = 0; 
  
  function void get_max_min_addr(input int        slave_no=0,
                                 input bit [7:0]  core_id =0,
                                output bit [35:0] min_addr,
                                output bit [35:0] max_addr);

     case(slave_no)
       0:  begin
              min_addr = 36'h0;    // MAILBOX_ST_ADDR = 'h10000000;
              max_addr = 36'hffff; // MAILBOX_END_ADDR = 'h1000ffff;
           end
       1:  begin
              min_addr = 36'h10000; //M_IFD0_ST_ADDR = 'h10010000;
              max_addr = 36'h1ffff; //M_IFD0_END_ADDR = 'h1001ffff;
           end
       2:  begin
              min_addr = 36'h20000; //M_IFD1_ST_ADDR = 'h10020000;
              max_addr = 36'h2ffff; //M_IFD1_END_ADDR = 'h1002ffff;
           end
       3:  begin
              min_addr = 36'h30000; //M_IFDW_ST_ADDR = 'h10030000;
              max_addr = 36'h3ffff; //M_IFDW_END_ADDR = 'h1003ffff;
           end
       4:  begin
              min_addr = 36'h40000; //M_ODR_ST_ADDR = 'h10040000;
              max_addr = 36'h4ffff; //M_ODR_END_ADDR = 'h1004ffff;
           end
       5:  begin
              min_addr = 36'h50000; //D_IFD0_ST_ADDR = 'h10050000;
              max_addr = 36'h5ffff; //D_IFD0_END_ADDR = 'h1005ffff;
           end
       6:  begin
              min_addr = 36'h60000; //D_IFD1_ST_ADDR = 'h10060000;
              max_addr = 36'h6ffff; //D_IFD1_END_ADDR = 'h1006ffff;
           end
       7:  begin
              min_addr = 36'h70000; //D_ODR_ST_ADDR = 'h10070000;
              max_addr = 36'h7ffff; //D_ODR_END_ADDR = 'h1007ffff;
           end
       8:  begin
              min_addr = 36'h80000; //TOKEN_ST_ADDR = 'h10080000;
              max_addr = 36'h8ffff; //TOKEN_END_ADDR = 'h1008ffff;
           end
       9:  begin
              min_addr = 36'h90000; //M_MVMEXE_ST_ADDR = 'h10090000;
              max_addr = 36'h9ffff; //M_MVMEXE_END_ADDR = 'h1009ffff;
           end
       10: begin
              min_addr = 36'ha0000; //M_MVMPRG_ST_ADDR = 'h100a0000;
              max_addr = 36'haffff; //M_MVMPRG_END_ADDR = 'h100affff;
           end
       11: begin
              min_addr = 36'hb0000; //M_IAU_ST_ADDR = 'h100b0000;
              max_addr = 36'hbffff; //M_IAU_END_ADDR = 'h100bffff;
           end
       12: begin
              min_addr = 36'hc0000; //M_DPU_ST_ADDR = 'h100c0000;
              max_addr = 36'hcffff; //M_DPU_END_ADDR = 'h100cffff;
           end
       13: begin
              min_addr = 36'hd0000; //D_DWPU_ST_ADDR = 'h100d0000;
              max_addr = 36'hdffff; //D_DWPU_END_ADDR = 'h100dffff;
           end
       14: begin
              min_addr = 36'he0000; //D_IAU_ST_ADDR = 'h100e0000;
              max_addr = 36'heffff; //D_IAU_END_ADDR = 'h100effff;
           end
       15: begin
              min_addr = 36'hf0000; //D_DPU_ST_ADDR = 'h100f0000;
              max_addr = 36'hfffff; //D_DPU_END_ADDR = 'h100fffff;
           end
       16: begin
              min_addr = 36'h100000; //CSR_ST_ADDR = 'h10100000;
              max_addr = 36'h10ffff; //CSR_END_ADDR = 'h1010ffff;
           end
       17: begin
              min_addr = 36'h110000; //DMA_ST_ADDR = 'h10110000;
              max_addr = 36'h11ffff; //DMA_END_ADDR = 'h1011ffff;
           end
//       18: begin
//              min_addr = 36'h120000; //PLIC_ST_ADDR = 'h10120000;
//              max_addr = 36'h21ffff; //PLIC_END_ADDR = 'h1021ffff;
//           end
       18: begin
              min_addr = 36'h220000; //PVT_ST_ADDR = 'h10220000;
              max_addr = 36'h220020; //36'h22ffff; //PVT_END_ADDR = 'h1022ffff;
           end
       19: begin
              min_addr = 36'h230000; //PMU_ST_ADDR = 'h10230000;
              max_addr = 36'h23ffff; //PMU_END_ADDR = 'h1023ffff;
           end
       20: begin
              min_addr = 36'h400000; //PLIC_ST_ADDR = 'h10400000;
              max_addr = 36'h7fffff; //PLIC_END_ADDR = 'h107fffff;
           end
       21: begin
              min_addr = 36'h800_0000; //HP Local L1
              max_addr = 36'h83f_ffff; //
           end
       22: begin
              min_addr = 36'h8000_0000; // DDR R0 over HP NOc
              max_addr = 36'hffff_ffff; //
           end
       23: begin
              min_addr = 36'h8_8000_0000; // DDR R1 over HP NOc
              max_addr = 36'h8_ffff_ffff; //
           end
       24: begin
              min_addr = 36'h800_0000; // L2
              max_addr = 36'h9ff_ffff; //
           end
       25: begin
              min_addr = 36'h002_0000; // L2
              max_addr = 36'h002_ffff; //
           end
       endcase
       if(slave_no < 22)
       begin
         min_addr[35:28] = core_id;
         max_addr[35:28] = core_id;
       end
       `uvm_info("get_max_min_addr",
       $psprintf("slave_no=%0d , core_id=%0d, min_addr=%0h max_addr=%0h",
       slave_no, core_id, min_addr, max_addr), UVM_LOW)
  endfunction : get_max_min_addr

//  typedef svt_axi_transaction::resp_type_enum axi_resp_type_enum;

  function automatic bit [1:0]  check_slv_resp
                              (input int        lp_system=0,
                               input int        slave_no=0,
                               input bit [7:0]  core_id =0,
                               input bit [35:0] addr);
     bit [2:0] axi_resp;

     case(slave_no)
       0:  begin
              if(addr[15:0] inside {16'h0,[16'h38:16'h20],16'h48})
                 axi_resp = 2'd0;
              else
                 axi_resp = 2'd2;
           end
       16: begin
              if(addr[15:0] inside {[16'h0:16'hd0]})
                 axi_resp = 2'd0;
              else
                 axi_resp = 2'd2; //CSR_ST_ADDR = 'h10100000;
           end
       17: begin
              if(addr[15:0] inside {[16'h78:16'h0]})
                 axi_resp = 2'd0;
              else
                 axi_resp = 2'd2; //DMA_END_ADDR = 'h1011ffff;
           end
       19: begin
              if(addr[15:0] inside {[16'h0:16'h28]})
                 axi_resp = 2'd0;
              else
                 axi_resp = 2'd2; //PMU_END_ADDR = 'h1023ffff;
           end
       25: begin
              if(lp_system == 1)
                 axi_resp = 2'd3;
              else
                 axi_resp = 2'd0;
           end
       default : axi_resp = 2'd0;
      endcase

      return axi_resp;
    endfunction : check_slv_resp


    //This is to check the hart_unavail_async_o signal. hart should be availble only when the ax25_clk_en is 1 and hart_unavail is 0.
    // https://git.axelera.ai/ai-hw-team/triton/-/issues/2561
    // TODO UNCOMENT ONCE BUG FIX MERGED
    always @ (hart_unavail_async_o or hart_unavail_async) begin
      `uvm_info ("SIDEBAND_SIGNAL_SVA",$sformatf("Enter into before SVA CHECKS"),UVM_LOW)
       #1;
      // RESET_GEN_TEST dependency added here
      SIDEBAND_SIGNAL_1_SVA: assert (hart_unavail_async_o === ((~ax25_clk_en_signal)| hart_unavail_async)) begin
        `uvm_info ("REST_GEN_SVA",$sformatf("SVA CHECKS: Stage0 : PASS:hart_unavail_async_o =%0b,ax25_clk_en_signal=%0b,hart_unavail_async=%0h",hart_unavail_async_o,ax25_clk_en_signal,hart_unavail_async),UVM_LOW)
      end
      else begin
        `uvm_error("REST_GEN_SVA",$sformatf("SVA CHECKS: Stage0 : FAIL:hart_unavail_async_o =%0b,ax25_clk_en_signal=%0b,hart_unavail_async=%0h",hart_unavail_async_o,ax25_clk_en_signal,hart_unavail_async))
      end
    end
    

endinterface

`endif // GUARD_AI_CORE_INFRA_CONFIG_IF_SVI
