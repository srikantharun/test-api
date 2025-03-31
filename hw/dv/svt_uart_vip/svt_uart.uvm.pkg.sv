ifndef GUARD_SVT_AMBA_UVM_PKG
`define GUARD_SVT_AMBA_UVM_PKG

// Enable AXI to CHI mapping. Do not remove this line.
`ifdef SVT_AMBA_OPTIMIZED_COMPILE
  `ifdef  SVT_AMBA_INCLUDE_CHI_IN_AMBA_SYS_ENV
    `define SVT_AMBA_AXI_TO_CHI_MAP_ENABLE
  `endif
  `ifndef SVT_AMBA_VCAP_ENABLE
   `ifndef SVT_EXCLUDE_VCAP
     `define SVT_EXCLUDE_VCAP
   `endif
  `endif
`endif

`ifdef SVT_AMBA_VCAP_ENABLE
  // Temporary: enable this macro for multi output events for same traffic profile
  `define SVT_ENABLE_VCAP_MULTI_OUPUT_EVENT
`endif

`ifdef DESIGNWARE_INCDIR
  `define SVT_AMBA_LOADER_FILE `"`DESIGNWARE_INCDIR/vip/svt/common/latest/sverilog/include/svt_bootloader.svi`"
    `include `SVT_AMBA_LOADER_FILE
`ifndef SVT_ENABLE_DISCRETE_LIBRARY_FLOW
  `include `SVT_SOURCE_MAP_LIB_INCLUDE_PKG(S-2021.12,svt.uvm)
`endif
`else
  `include "svt_bootloader.svi"
`ifndef SVT_ENABLE_DISCRETE_LIBRARY_FLOW
  `include "svt.uvm.pkg"
`endif
`endif


`ifndef SVT_ENABLE_DISCRETE_LIBRARY_FLOW
`ifdef SVT_AMBA_ENABLE_C_BASED_MEM
 `ifdef DESIGNWARE_INCDIR
  `include `SVT_SOURCE_MAP_LIB_INCLUDE_PKG(S-2021.12,svt_mem.uvm)
 `else
  `include "svt_mem.uvm.pkg"
 `endif
`endif
`endif

`ifdef  SVT_AMBA_INCLUDE_CHI_IN_AMBA_SYS_ENV
  `include "svt_chi_if.svi"
`endif

`ifndef SVT_AMBA_OPTIMIZED_COMPILE
  `include "svt_axi_if.svi"
`ifndef SVT_AMBA_EXCLUDE_AHB_IN_AMBA_SYS_ENV
  `include "svt_ahb_if.svi"
`endif
`ifndef SVT_AMBA_EXCLUDE_APB_IN_AMBA_SYS_ENV
  `include "svt_apb_if.svi"
`endif
`endif

`ifdef SVT_AMBA_OPTIMIZED_COMPILE
  `include "svt_axi.uvm.pkg"
`ifdef  SVT_AMBA_INCLUDE_CHI_IN_AMBA_SYS_ENV
  `include "svt_chi_source.uvm.pkg"
  `include "svt_chi_sequence.uvm.pkg"
  `include "svt_chi.uvm.pkg"
`endif

`ifndef SVT_AMBA_EXCLUDE_AHB_IN_AMBA_SYS_ENV
  `include "svt_ahb.uvm.pkg"
`endif

`ifndef SVT_AMBA_EXCLUDE_APB_IN_AMBA_SYS_ENV
  `include "svt_apb.uvm.pkg"
`endif 
`endif


package svt_amba_uvm_pkg;

 import uvm_pkg::*;

 import svt_uvm_pkg::*;
`ifdef SVT_AMBA_ENABLE_C_BASED_MEM
 import svt_mem_uvm_pkg::*;
`endif


`ifdef SVT_AMBA_OPTIMIZED_COMPILE
    import svt_axi_uvm_pkg::*;
  `ifdef  SVT_AMBA_INCLUDE_CHI_IN_AMBA_SYS_ENV
     import svt_chi_source_uvm_pkg::*;
     import svt_chi_sequence_uvm_pkg::*;
     import svt_chi_uvm_pkg::*;
  `endif
  `ifndef SVT_AMBA_EXCLUDE_AHB_IN_AMBA_SYS_ENV
    import svt_ahb_uvm_pkg::*;
  `endif
  `ifndef SVT_AMBA_EXCLUDE_APB_IN_AMBA_SYS_ENV
    import svt_apb_uvm_pkg::*;
  `endif  
`endif

`ifndef SVT_AMBA_OPTIMIZED_COMPILE
   typedef virtual svt_axi_if svt_axi_vif;
   typedef virtual svt_axi_master_if svt_axi_master_vif;
   typedef virtual svt_axi_slave_if svt_axi_slave_vif;
  
  `ifdef  SVT_AMBA_INCLUDE_CHI_IN_AMBA_SYS_ENV
     typedef virtual svt_chi_if svt_chi_vif;
     typedef virtual svt_chi_rn_if svt_chi_rn_vif;
     typedef virtual svt_chi_sn_if svt_chi_sn_vif;
  `endif
   
  `ifndef SVT_AMBA_EXCLUDE_AHB_IN_AMBA_SYS_ENV
    typedef virtual svt_ahb_if svt_ahb_vif;
    typedef virtual svt_ahb_master_if svt_ahb_master_vif;
    typedef virtual svt_ahb_slave_if svt_ahb_slave_vif;
  `endif
  
  `ifndef SVT_AMBA_EXCLUDE_APB_IN_AMBA_SYS_ENV
    typedef virtual svt_apb_if svt_apb_vif;
    typedef virtual svt_apb_slave_if svt_apb_slave_vif;
  `endif
`endif //  `ifndef SVT_AMBA_OPTIMIZED_COMPILE
  

`ifdef SVT_AMBA_OPTIMIZED_COMPILE
  `include "svt_amba_source.uvm.svi"
  `include `SVT_SOURCE_MAP_MODEL_INCLUDE_SVI(amba_svt,amba_system_monitor_svt,S-2021.12,svt_amba_system_monitor_source.uvm)

  `ifdef  SVT_AMBA_INCLUDE_CHI_IN_AMBA_SYS_ENV
    `ifndef SVT_CHI_EXCLUDE_CHI_SYSTEM_MON
      `include `SVT_SOURCE_MAP_MODEL_INCLUDE_SVI(amba_svt,chi_system_monitor_svt,S-2021.12,svt_chi_system_monitor_source)
    `endif
    `include `SVT_SOURCE_MAP_ENV_INCLUDE_SVI(amba_svt,chi_system_env_svt,S-2021.12,svt_chi_system_env_optimized_compile_source.uvm)
  `endif

  `ifdef SVT_AMBA_MULTI_CHIP_SYSTEM_MONITOR_INTERNAL_ENABLE
    `include `SVT_SOURCE_MAP_MODEL_INCLUDE_SVI(amba_svt,amba_multi_chip_system_monitor_svt,S-2021.12,svt_amba_multi_chip_system_monitor_source)
  `endif

  `include `SVT_SOURCE_MAP_ENV_INCLUDE_SVI(amba_svt,amba_system_env_svt,S-2021.12,svt_amba_system_env_optimized_compile_source.uvm)
`endif //  `ifdef SVT_AMBA_OPTIMIZED_COMPILE
  

`ifndef SVT_AMBA_OPTIMIZED_COMPILE 
  `include `SVT_SOURCE_MAP_MODEL_CMD_INCLUDE_SVI(amba_svt,amba_system_env_svt,S-2021.12,svt_amba_system_env_source.uvm)
`endif

endpackage

`endif //GUARD_SVT_AMBA_UVM_PKG
[gitlab-runner@htz1-glcitest saruna]$ 
[gitlab-runner@htz1-glcitest saruna]$ cat /home/projects/europa_vip/i2c_env_svt/include/sverilog/svt_i2c.uvm.pkg
`ifndef GUARD_SVT_I2C_UVM_PKG
`define GUARD_SVT_I2C_UVM_PKG

//`include "svt.uvm.pkg"
//`include "svt_bfm_shell.uvm.pkg"
`ifdef DESIGNWARE_INCDIR
  `define SVT_I2C_LOADER_FILE `"`DESIGNWARE_INCDIR/vip/svt/common/latest/sverilog/include/svt_bootloader.svi`"
  `include `SVT_I2C_LOADER_FILE 
`ifndef SVT_ENABLE_DISCRETE_LIBRARY_FLOW
  `include `SVT_SOURCE_MAP_LIB_INCLUDE_PKG(S-2021.12,svt.uvm)
  `include `SVT_SOURCE_MAP_LIB_INCLUDE_PKG(S-2021.12,svt_bfm_shell.uvm)
`endif
  `define SVT_I2C_NVS_LOADER_FILE `"`DESIGNWARE_INCDIR/vip/svt/i2c_svt/latest/sverilog/include/svt_i2c_nvs_loader_util.svi`"
  `include `SVT_I2C_NVS_LOADER_FILE
`else
 `include "svt_bootloader.svi"
  `include "svt_i2c_nvs_loader_util.svi"
`ifndef SVT_ENABLE_DISCRETE_LIBRARY_FLOW
  `include "svt.uvm.pkg"
  `include "svt_bfm_shell.uvm.pkg"
`endif
`endif

`include "svt_i2c_if.svi"
`include "svt_i2c_sys_if.svi"

//`include "svt_i2c_sv_enum_pkg.sv"
`include `SVT_SOURCE_MAP_SUITE_MODULE(i2c_svt,S-2021.12,svt_i2c_sv_enum_pkg)

`ifndef SVT_BFM_SHELL_VMT_VRT_MODEL
`define SVT_BFM_SHELL_VMT_VRT_MODEL
`endif

// This macro must be unset so that a pure SVT model can be loaded after
// an SVT OVM Wrapper model.
`undef SVT_BFM_SHELL_VMT_VRT_MODEL
 
//--------------------------------------------------------------------------
// Package svt_i2c_uvm_pkg;
//--------------------------------------------------------------------------
package svt_i2c_uvm_pkg;
  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  import svt_bfm_shell_uvm_pkg::*;
  import svt_i2c_enum_pkg::*;

  // Type Definitions
  typedef virtual svt_i2c_if svt_i2c_vif;
  
  `include "uvm_macros.svh"
  //`include "svt_i2c_source.uvm.svi"
  `include `SVT_SOURCE_MAP_ENV_INCLUDE_SVI(i2c_svt,i2c_env_svt,S-2021.12,svt_i2c_env_source.uvm)  

endpackage // svt_i2c_uvm_pkg
   
`ifndef SVT_I2C_UNIT_TEST
//`include "svt_i2c_env_wrappers.svi"
  `include `SVT_SOURCE_MAP_ENV_INCLUDE_SVI(i2c_svt,i2c_env_svt,S-2021.12,svt_i2c_env_wrappers)  
`ifndef __SVDOC__
  `include `SVT_SOURCE_MAP_MODEL_INCLUDE_SVI(i2c_svt,i2c_master_svt,S-2021.12,svt_i2c_nvs_master_source.uvm)  
  `include `SVT_SOURCE_MAP_MODEL_INCLUDE_SVI(i2c_svt,i2c_slave_svt,S-2021.12,svt_i2c_nvs_slave_source.uvm)  
`endif     
`endif
`endif // `ifndef GUARD_SVT_I2C_UVM_PKG
[gitlab-runner@htz1-glcitest saruna]$ cat /home/projects/europa_vip/uart_agent_svt/include/sverilog/svt_uart.uvm.pkg
//--------------------------------------------------------------------------
// COPYRIGHT (C) 2012, 2013 SYNOPSYS INC.
// This software and the associated documentation are confidential and
// proprietary to Synopsys, Inc. Your use or disclosure of this software
// is subject to the terms and conditions of a written license agreement
// between you, or your company, and Synopsys, Inc. In the event of
// publications, the following notice is applicable:
//
// ALL RIGHTS RESERVED
//
// The entire notice above must be reproduced on all authorized copies.
//--------------------------------------------------------------------------
`ifndef GUARD_SVT_UART_UVM_PKG
 `define GUARD_SVT_UART_UVM_PKG
  `ifndef SVT_UART
  `define SVT_UART
  `endif
`ifdef SVT_UART_SLED_RECORD_ENABLE
  `ifndef SVT_SLED_RECORD_ENABLE
    `define SVT_SLED_RECORD_ENABLE
  `endif
`endif
`ifdef DESIGNWARE_INCDIR
  `define SVT_UART_LOADER_FILE `"`DESIGNWARE_INCDIR/vip/svt/common/latest/sverilog/include/svt_bootloader.svi`"
  `include `SVT_UART_LOADER_FILE 
`ifndef SVT_ENABLE_DISCRETE_LIBRARY_FLOW
  `include `SVT_SOURCE_MAP_LIB_INCLUDE_PKG(S-2021.12,svt.uvm)
  `include `SVT_SOURCE_MAP_LIB_INCLUDE_PKG(S-2021.12,svt_bfm_shell.uvm)
`endif
  `define SVT_UART_NVS_LOADER_FILE `"`DESIGNWARE_INCDIR/vip/svt/uart_svt/latest/sverilog/include/svt_uart_nvs_loader_utils.svi`"
  `include `SVT_UART_NVS_LOADER_FILE 
`else
  `include "svt_bootloader.svi"
`ifndef SVT_ENABLE_DISCRETE_LIBRARY_FLOW
  `include "svt.uvm.pkg"
  `include "svt_bfm_shell.uvm.pkg"
`endif
`endif
`include "svt_uart_nvs_loader_utils.svi"

`include "svt_uart_if.svi"

//--------------------------------------------------------------------------
// Package svt_uart_uvm_pkg;
//--------------------------------------------------------------------------
package svt_uart_uvm_pkg;

  import uvm_pkg::*;
  import svt_uvm_pkg::*;
`include "uvm_macros.svh"

  import svt_bfm_shell_uvm_pkg::*;
  // Type Definitions
  typedef virtual svt_uart_if svt_uart_vif;

`include "svt_uart_source.uvm.svi"
`include `SVT_SOURCE_MAP_AGENT_INCLUDE_SVI(uart_svt,uart_agent_svt,S-2021.12,svt_uart_agent_source.uvm)
endpackage : svt_uart_uvm_pkg
 
`ifdef SVT_UART
`ifndef __SVDOC__
import svt_uart_uvm_pkg::*;
`endif
`endif
`ifndef SVT_UART_UNIT_TEST
`include "svt_uart_wrapper.svi"
`endif
`endif //  `ifndef GUARD_SVT_UART_UVM_PKG
   
//--------------------------------------------------------------------------
//----------------------END OF FILE-----------------------------------------
//--------------------------------------------------------------------------
   

