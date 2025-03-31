//
// File: lpddr_subsystem_params_pkg.sv
//
// Generated from Questa VIP Configurator (20240520)
// Generated using Questa VIP Library ( 2024.2 : 05/29/2024:10:31 )
//
package lpddr_subsystem_params_pkg;
    import addr_map_pkg::*;
    import rw_delay_db_pkg::*;
    //
    // Import the necessary QVIP packages:
    //
    import mgc_apb3_v1_0_pkg::*;
    import mgc_apb_seq_pkg::*;
    import mgc_axi4_v1_0_pkg::*;
    import mgc_axi4_seq_pkg::*;
    class apb_master_0_params;
        localparam int APB3_SLAVE_COUNT      = 1;
        localparam int APB3_PADDR_BIT_WIDTH  = 32;
        localparam int APB3_PWDATA_BIT_WIDTH = 32;
        localparam int APB3_PRDATA_BIT_WIDTH = 32;
    endclass: apb_master_0_params
    
    typedef apb3_vip_config #(apb_master_0_params::APB3_SLAVE_COUNT,apb_master_0_params::APB3_PADDR_BIT_WIDTH,apb_master_0_params::APB3_PWDATA_BIT_WIDTH,apb_master_0_params::APB3_PRDATA_BIT_WIDTH) apb_master_0_cfg_t;
    // Not required param seperate 
    typedef apb3_vip_config #(apb_master_0_params::APB3_SLAVE_COUNT,(apb_master_0_params::APB3_PADDR_BIT_WIDTH-16),apb_master_0_params::APB3_PWDATA_BIT_WIDTH,apb_master_0_params::APB3_PRDATA_BIT_WIDTH) apb_master_1_cfg_t;
    
    typedef apb_agent #(apb_master_0_params::APB3_SLAVE_COUNT,apb_master_0_params::APB3_PADDR_BIT_WIDTH,apb_master_0_params::APB3_PWDATA_BIT_WIDTH,apb_master_0_params::APB3_PRDATA_BIT_WIDTH) apb_master_0_agent_t;
    typedef apb_agent #(apb_master_0_params::APB3_SLAVE_COUNT,apb_master_0_params::APB3_PADDR_BIT_WIDTH-16,apb_master_0_params::APB3_PWDATA_BIT_WIDTH,apb_master_0_params::APB3_PRDATA_BIT_WIDTH) apb_master_1_agent_t;
    
    typedef virtual mgc_apb3 #(apb_master_0_params::APB3_SLAVE_COUNT,apb_master_0_params::APB3_PADDR_BIT_WIDTH,apb_master_0_params::APB3_PWDATA_BIT_WIDTH,apb_master_0_params::APB3_PRDATA_BIT_WIDTH) apb_master_0_bfm_t;
    typedef virtual mgc_apb3 #(apb_master_0_params::APB3_SLAVE_COUNT,apb_master_0_params::APB3_PADDR_BIT_WIDTH-16,apb_master_0_params::APB3_PWDATA_BIT_WIDTH,apb_master_0_params::APB3_PRDATA_BIT_WIDTH) apb_master_1_bfm_t;


    // For RAL use
    typedef apb3_host_apb3_transaction #(apb_master_0_params::APB3_SLAVE_COUNT, apb_master_0_params::APB3_PADDR_BIT_WIDTH, apb_master_0_params::APB3_PWDATA_BIT_WIDTH, apb_master_0_params::APB3_PRDATA_BIT_WIDTH)apb3_host_trans_t; 
    typedef reg2apb_adapter #(apb3_host_trans_t, apb_master_0_params::APB3_SLAVE_COUNT, apb_master_0_params::APB3_PADDR_BIT_WIDTH, apb_master_0_params::APB3_PWDATA_BIT_WIDTH, apb_master_0_params::APB3_PRDATA_BIT_WIDTH) reg2apb_adapter_t; 
    typedef apb_reg_predictor #(apb3_host_trans_t, apb_master_0_params::APB3_SLAVE_COUNT, apb_master_0_params::APB3_PADDR_BIT_WIDTH, apb_master_0_params::APB3_PWDATA_BIT_WIDTH, apb_master_0_params::APB3_PRDATA_BIT_WIDTH) apb_reg_predictor_t;

    
    class axi4_master_0_params;
        localparam int AXI4_ADDRESS_WIDTH   = 33;
        localparam int AXI4_RDATA_WIDTH     = 256;
        localparam int AXI4_WDATA_WIDTH     = 256;
        localparam int AXI4_ID_WIDTH        = 8;
        localparam int AXI4_USER_WIDTH      = 1;
        localparam int AXI4_REGION_MAP_SIZE = 16;
    endclass: axi4_master_0_params

    parameter int MEMC_BURST_LENGTH    = 16;
    parameter int MEMC_FREQ_RATIO      = 4;
    parameter int MEMC_DRAM_DATA_WIDTH = 32;
    parameter int MEMC_NUM_OF_ENTRY    = 64;
    parameter int UMCTL2_A_ADDRW       = 33;
    parameter int UMCTL2_A_ADDRW_1     = 32;
    parameter int FULL_BUS_WIDTH       = 0;
    parameter int HALF_BUS_WIDTH       = 1;
    parameter int HIF_DOWN_1           = $clog2(MEMC_BURST_LENGTH);
    //TODO: pass parameter in below line instead of FULL_BUS_WIDTH by configuring it through APB by ifdef
    parameter int AXI_DOWN_1           = ($clog2(MEMC_BURST_LENGTH))+($clog2(MEMC_DRAM_DATA_WIDTH/(8*(2**FULL_BUS_WIDTH))));
    
    typedef axi4_vip_config #(axi4_master_0_params::AXI4_ADDRESS_WIDTH,axi4_master_0_params::AXI4_RDATA_WIDTH,axi4_master_0_params::AXI4_WDATA_WIDTH,axi4_master_0_params::AXI4_ID_WIDTH,axi4_master_0_params::AXI4_USER_WIDTH,axi4_master_0_params::AXI4_REGION_MAP_SIZE) axi4_master_0_cfg_t;
    
    typedef axi4_master_rw_transaction #(axi4_master_0_params::AXI4_ADDRESS_WIDTH,axi4_master_0_params::AXI4_RDATA_WIDTH,axi4_master_0_params::AXI4_WDATA_WIDTH,axi4_master_0_params::AXI4_ID_WIDTH,axi4_master_0_params::AXI4_USER_WIDTH,axi4_master_0_params::AXI4_REGION_MAP_SIZE)axi_trans_t; 

    typedef axi4_agent #(axi4_master_0_params::AXI4_ADDRESS_WIDTH,axi4_master_0_params::AXI4_RDATA_WIDTH,axi4_master_0_params::AXI4_WDATA_WIDTH,axi4_master_0_params::AXI4_ID_WIDTH,axi4_master_0_params::AXI4_USER_WIDTH,axi4_master_0_params::AXI4_REGION_MAP_SIZE) axi4_master_0_agent_t;
    
    typedef virtual mgc_axi4 #(axi4_master_0_params::AXI4_ADDRESS_WIDTH,axi4_master_0_params::AXI4_RDATA_WIDTH,axi4_master_0_params::AXI4_WDATA_WIDTH,axi4_master_0_params::AXI4_ID_WIDTH,axi4_master_0_params::AXI4_USER_WIDTH,axi4_master_0_params::AXI4_REGION_MAP_SIZE) axi4_master_0_bfm_t;
    
    //
    // `includes for the config policy classes:
    //
    `include "apb_master_0_config_policy.svh"
    `include "apb_master_1_config_policy.svh"
    `include "axi4_master_0_config_policy.svh"
endpackage: lpddr_subsystem_params_pkg
