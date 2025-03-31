// *** (C) Copyright Axelera AI 2021        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : srinivas.prakash@axelera.ai  *** //

`ifndef __AXI_TRACKER_PKG_DEFINE__ 
`define __AXI_TRACKER_PKG_DEFINE__

package axi_tracker_pkg;

  import axi_pkg::*;

  // Object classes
  `include "axi_tracker_aw_channel_obj.svh"
  `include "axi_tracker_w_channel_obj.svh"
  `include "axi_tracker_b_channel_obj.svh"
  `include "axi_tracker_ar_channel_obj.svh"
  `include "axi_tracker_r_channel_obj.svh"

endpackage : axi_tracker_pkg

`endif // __AXI_TRACKER_PKG_DEFINE__
