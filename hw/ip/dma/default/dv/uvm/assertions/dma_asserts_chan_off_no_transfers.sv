// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Check Behaviour of DMA DUT when all channels are off
// Owner      : Sultan Khan

`ifndef __CHAN_OFF_NO_TRANSFERS__ 
`define __CHAN_OFF_NO_TRANSFERS__

  import uvm_pkg::*;
  `include "uvm_macros.svh"

module  dma_asserts_chan_off_no_transfers 
(
  input  logic       i_clk,
  input  logic       i_rst_n,

  // AXI-SLAVE IF (register Interface)
  input  logic       i_axi_s_awvalid,
  input  logic       o_axi_s_awready,
  input  logic       i_axi_s_wvalid,
  input  logic       o_axi_s_wready,
  input  logic       o_axi_s_bvalid,
  input  logic       i_axi_s_bready,
  input  logic       i_axi_s_arvalid,
  input  logic       o_axi_s_arready,
  input  logic       o_axi_s_rvalid,
  input  logic       i_axi_s_rready,

  // AXI-MASTER IF (DMA Transfer Ports)
  input  logic       o_axi_m_awvalid[2],
  input  logic       i_axi_m_awready[2],
  input  logic       o_axi_m_wvalid[2],
  input  logic       i_axi_m_wready[2],
  input  logic       i_axi_m_bvalid[2],
  input  logic       o_axi_m_bready[2],
  input  logic       o_axi_m_arvalid[2],
  input  logic       i_axi_m_arready[2],
  input  logic       i_axi_m_rvalid[2],
  input  logic       o_axi_m_rready[2]
);


// Mirror Signals (probes into lower level hierarchies)
logic  mirror_chan0_enable;
logic  mirror_chan1_enable;
logic  mirror_chan2_enable;
logic  mirror_chan3_enable;

// assist in creating conditions
logic  any_channel_enabled;



// Grab ENABLE status of each Channel
assign mirror_chan0_enable = g_chnl[0].u_chnl.u_csr.ch_ctrl_enable_qs;
assign mirror_chan1_enable = g_chnl[1].u_chnl.u_csr.ch_ctrl_enable_qs;
assign mirror_chan2_enable = g_chnl[2].u_chnl.u_csr.ch_ctrl_enable_qs;
assign mirror_chan3_enable = g_chnl[3].u_chnl.u_csr.ch_ctrl_enable_qs;
assign mirror_chan0_mode   = u_progif.u_csr.ch_mode_ch0_mode_qs;
assign mirror_chan1_mode   = u_progif.u_csr.ch_mode_ch1_mode_qs;
assign mirror_chan2_mode   = u_progif.u_csr.ch_mode_ch2_mode_qs;
assign mirror_chan3_mode   = u_progif.u_csr.ch_mode_ch3_mode_qs;


assign any_channel_enabled = |{ mirror_chan0_enable, mirror_chan0_mode,
                                mirror_chan1_enable, mirror_chan1_mode,
                                mirror_chan2_enable, mirror_chan2_mode,
                                mirror_chan3_enable, mirror_chan3_mode };


// ------------------------------------------------------------------------
// When all channels are disabled, there must be no AxVALIDs from the DUT
// ------------------------------------------------------------------------

  // Whenever AXVALIDs are raised, at least 1 channel must be enabled (So never when all channels are Disabled)
  property AXVALID_WHEN_CHAN_ENABLED (axvalid);
    @(posedge i_clk) disable iff (~i_rst_n)  ($rose(axvalid)) |-> (any_channel_enabled == 1);
  endproperty


  // AXI_SLAVE I/F of DUT (Register Interface) 
  // We dont have AXVALID Assertions on this interface, as axi-transactions may be instigated to enable a channel

  // AXI_MASTER I/F of DUT (DMA Transfer Ports 0 and 1) 
  
  // PORT0
  ASSERT_AWVALID_WHEN_CHAN_ENABLED_PORT0   : assert property (AXVALID_WHEN_CHAN_ENABLED(o_axi_m_awvalid[0]))  
                                             else `uvm_error("DMA ASSERT FAIL", $sformatf("DUT_DMA_PORT0   : AWVALID Asserted when no channels are ENABLED"))

  ASSERT_ARVALID_WHEN_CHAN_ENABLED_PORT0   : assert property (AXVALID_WHEN_CHAN_ENABLED(o_axi_m_arvalid[0]))  
                                             else `uvm_error("DMA ASSERT FAIL", $sformatf("DUT_DMA_PORT0   : ARVALID Asserted when no channels are ENABLED"))

  ASSERT_WVALID_WHEN_CHAN_ENABLED_PORT0    : assert property (AXVALID_WHEN_CHAN_ENABLED(o_axi_m_wvalid[0]))  
                                             else `uvm_error("DMA ASSERT FAIL", $sformatf("DUT_DMA_PORT0   : WVALID Asserted when no channels are ENABLED"))


  // PORT1
  ASSERT_AWVALID_WHEN_CHAN_ENABLED_PORT1   : assert property (AXVALID_WHEN_CHAN_ENABLED(o_axi_m_awvalid[1]))  
                                             else `uvm_error("DMA ASSERT FAIL", $sformatf("DUT_DMA_PORT1   : AWVALID Asserted when no channels are ENABLED"))

  ASSERT_ARVALID_WHEN_CHAN_ENABLED_PORT1   : assert property (AXVALID_WHEN_CHAN_ENABLED(o_axi_m_arvalid[1]))  
                                             else `uvm_error("DMA ASSERT FAIL", $sformatf("DUT_DMA_PORT1   : ARVALID Asserted when no channels are ENABLED"))

  ASSERT_WVALID_WHEN_CHAN_ENABLED_PORT1    : assert property (AXVALID_WHEN_CHAN_ENABLED(o_axi_m_wvalid[1]))  
                                             else `uvm_error("DMA ASSERT FAIL", $sformatf("DUT_DMA_PORT1   : WVALID Asserted when no channels are ENABLED"))


// ------------------------------------------------------------------------
// When all channels are disabled, there must be no AXI-Transfers of anykind, on any of the 3 AXI Interfaces
// ------------------------------------------------------------------------

  // AXI Transfers ONLY when any channel is enabled (So never when all channels are Disabled)
  property TRANSFERS_WHEN_CHAN_ENABLED (axvalid, axready);
    @(posedge i_clk) disable iff (~i_rst_n)  (axvalid & axready) |-> (any_channel_enabled == 1);
  endproperty

  // AXI_SLAVE I/F of DUT (Register Interface) 
  // We dont have AX Transfer Assertions on this interface, as axi-transactions may be instigated to enable a channel


  // AXI_MASTER I/F of DUT (DMA Transfer Ports 0 and 1) 

  // PORT0
  ASSERT_AW_TRANSFERS_WHEN_CHAN_ENABLED_PORT0   : assert property (TRANSFERS_WHEN_CHAN_ENABLED(o_axi_m_awvalid[0], i_axi_m_awready[0]))  
                                                   else `uvm_error("DMA ASSERT FAIL", $sformatf("DUT_DMA_PORT0   : AW Transfers seen when no channels are ENABLED"))

  ASSERT_W_TRANSFERS_WHEN_CHAN_ENABLED_PORT0    : assert property (TRANSFERS_WHEN_CHAN_ENABLED(o_axi_m_wvalid[0], i_axi_m_wready[0]))  
                                                   else `uvm_error("DMA ASSERT FAIL", $sformatf("DUT_DMA_PORT0   : W (DATA) Transfers seen when no channels are ENABLED"))

  ASSERT_B_TRANSFERS_WHEN_CHAN_ENABLED_PORT0    : assert property (TRANSFERS_WHEN_CHAN_ENABLED(i_axi_m_bvalid[0], o_axi_m_bready[0]))  
                                                   else `uvm_error("DMA ASSERT FAIL", $sformatf("DUT_DMA_PORT0   : B (RESP) Transfers seen when no channels are ENABLED"))

  ASSERT_AR_TRANSFERS_WHEN_CHAN_ENABLED_PORT0   : assert property (TRANSFERS_WHEN_CHAN_ENABLED(o_axi_m_arvalid[0], i_axi_m_arready[0]))  
                                                   else `uvm_error("DMA ASSERT FAIL", $sformatf("DUT_DMA_PORT0   : AR Transfers seen when no channels are ENABLED"))

  ASSERT_R_TRANSFERS_WHEN_CHAN_ENABLED_PORT0    : assert property (TRANSFERS_WHEN_CHAN_ENABLED(i_axi_m_rvalid[0], o_axi_m_rready[0]))  
                                                   else `uvm_error("DMA ASSERT FAIL", $sformatf("DUT_DMA_PORT0   : R (DATA) Transfers seen when no channels are ENABLED"))
  
  // PORT1
  ASSERT_AW_TRANSFERS_WHEN_CHAN_ENABLED_PORT1   : assert property (TRANSFERS_WHEN_CHAN_ENABLED(o_axi_m_awvalid[1], i_axi_m_awready[1]))  
                                                   else `uvm_error("DMA ASSERT FAIL", $sformatf("DUT_DMA_PORT1   : AW Transfers seen when no channels are ENABLED"))

  ASSERT_W_TRANSFERS_WHEN_CHAN_ENABLED_PORT1    : assert property (TRANSFERS_WHEN_CHAN_ENABLED(o_axi_m_wvalid[1], i_axi_m_wready[1]))  
                                                   else `uvm_error("DMA ASSERT FAIL", $sformatf("DUT_DMA_PORT1   : W (DATA) Transfers seen when no channels are ENABLED"))

  ASSERT_B_TRANSFERS_WHEN_CHAN_ENABLED_PORT1    : assert property (TRANSFERS_WHEN_CHAN_ENABLED(i_axi_m_bvalid[1], o_axi_m_bready[1]))  
                                                   else `uvm_error("DMA ASSERT FAIL", $sformatf("DUT_DMA_PORT1   : B (RESP) Transfers seen when no channels are ENABLED"))

  ASSERT_AR_TRANSFERS_WHEN_CHAN_ENABLED_PORT1   : assert property (TRANSFERS_WHEN_CHAN_ENABLED(o_axi_m_arvalid[1], i_axi_m_arready[1]))  
                                                   else `uvm_error("DMA ASSERT FAIL", $sformatf("DUT_DMA_PORT1   : AR Transfers seen when no channels are ENABLED"))

  ASSERT_R_TRANSFERS_WHEN_CHAN_ENABLED_PORT1    : assert property (TRANSFERS_WHEN_CHAN_ENABLED(i_axi_m_rvalid[1], o_axi_m_rready[1]))  
                                                   else `uvm_error("DMA ASSERT FAIL", $sformatf("DUT_DMA_PORT1   : R (DATA) Transfers seen when no channels are ENABLED"))
   


endmodule

`endif //__CHAN_OFF_NO_TRANSFERS__
