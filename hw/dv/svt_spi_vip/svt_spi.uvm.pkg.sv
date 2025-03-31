//-----------------------------------------------------------------------------
// COPYRIGHT (C) 2014-2020 SYNOPSYS INC.
// This software and the associated documentation are confidential and
// proprietary to Synopsys, Inc. Your use or disclosure of this software
// is subject to the terms and conditions of a written license agreement
// between you, or your company, and Synopsys, Inc. In the event of
// publications, the following notice is applicable:
//
// ALL RIGHTS RESERVED
//
// The entire notice above must be reproduced on all authorized copies.
//-----------------------------------------------------------------------------

`ifndef GUARD_SVT_SPI_UVM_PKG
`define GUARD_SVT_SPI_UVM_PKG

`ifdef DESIGNWARE_INCDIR
  `define SVT_SPI_LOADER_FILE `"`DESIGNWARE_INCDIR/vip/svt/common/latest/sverilog/include/svt_bootloader.svi`"
  `include `SVT_SPI_LOADER_FILE 
`ifndef SVT_ENABLE_DISCRETE_LIBRARY_FLOW
  `include `SVT_SOURCE_MAP_LIB_INCLUDE_PKG(S-2021.12,svt_mem.uvm)
`endif
`else
  `include "svt_bootloader.svi"
`ifndef SVT_ENABLE_DISCRETE_LIBRARY_FLOW
  `include "svt_mem.uvm.pkg"
`endif
`endif

`define SVT_SPI_PKG_LOAD
`include "svt_spi_if.svi"
`include "svt_spi_empspi_if.svi"
`include "svt_spi_sys_if.svi"

package svt_spi_uvm_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import svt_uvm_pkg::*;
  import svt_mem_uvm_pkg::*;

`ifndef __SVDOC__
  typedef virtual svt_spi_if svt_spi_vif; 
  typedef virtual svt_spi_empspi_if svt_spi_empspi_vif; 
  typedef virtual svt_spi_sys_if svt_spi_sys_vif; 
`endif

  `include `SVT_SOURCE_MAP_ENV_INCLUDE_SVI(spi_svt,spi_system_env_svt,S-2021.12,svt_spi_system_env_source)

endpackage

`endif // GUARD_SVT_SPI_UVM_PKG

