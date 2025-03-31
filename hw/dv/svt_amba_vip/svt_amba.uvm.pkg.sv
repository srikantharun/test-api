`ifndef GUARD_SVT_AMBA_UVM_PKG
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

