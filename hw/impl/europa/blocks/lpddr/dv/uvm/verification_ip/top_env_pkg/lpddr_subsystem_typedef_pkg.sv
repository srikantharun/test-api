//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_typedef_pkg.sv
// Unit        : lpddr_subsystem_typedef_pkg
//------------------------------------------------------------------------------
// Description : This file contains the Package for the various typedefs used by
//               LPDDR Subsystem Verification Environment.
//------------------------------------------------------------------------------
`ifndef LPDDR_SUBSYSTEM_TYPEDEF_PKG_SV
`define LPDDR_SUBSYSTEM_TYPEDEF_PKG_SV

package lpddr_subsystem_typedef_pkg;

  // AXI and APB Transaction typedefs
  //typedef axi4_master_rw_transaction #(`AXI_SLAVE_PARAMS_INST) axi4_subordinate_rw_trans_t;
  //typedef axi4_master_rw_transaction #(`AXI_MASTER_PARAMS_INST) axi4_manager_rw_trans_t;
  //typedef apb3_host_apb3_transaction #(`APB_MASTER_PARAMS_INST) apb_rw_trans_t;

  //------------------------------------------------------------------------------
  // Enum: axi4_lpr_hpr_e
  //------------------------------------------------------------------------------
  //  This is used to select <high_or_low_or_variable> priority request to the <axi4_master_rw_transaction> to indicate red or blue read address queue.
  // 
  // AXI4_LPR_TRAFFIC - Low-priority traffic, region-0 and 1, storage will be Blue address queue.
  // AXI4_HPR_TRAFFIC - High-priority traffic, region-2, storage will be Red address queue.
  // AXI4_VPR_TRAFFIC - Variable-priority traffic, region-1/2, storage will be Blue/Red address queue.
  //------------------------------------------------------------------------------
  typedef enum bit [1:0]
  {
      AXI4_LPR_TRAFFIC = 2'h0,
      AXI4_HPR_TRAFFIC = 2'h1,
      AXI4_VPR_TRAFFIC = 2'h2
  } axi4_lpr_hpr_e;

  //------------------------------------------------------------------------------
  // Enum: axi4_write_traffic_e
  //------------------------------------------------------------------------------
  //  This is used to select <normal_or_variable> priority request to the <axi4_master_rw_transaction> for write address queue.
  // 
  // AXI4_NPW_TRAFFIC - Normal-priority traffic.
  // AXI4_VPW_TRAFFIC - Variable-priority traffic.
  //------------------------------------------------------------------------------

  typedef enum bit
  {
      AXI4_NPW_TRAFFIC = 'b0,
      AXI4_VPW_TRAFFIC = 'b1
  } axi4_write_traffic_e;

	//------------------------------------------------------------------------------
  // enum: qd_group_e
  //------------------------------------------------------------------------------
  // This is used to select the type of quasi-dynamic register to be written 
  // 
  // QD_GROUP_1 - quasi-dynamic group 1 register 
  // QD_GROUP_2 - quasi-dynamic group 2 register 
  // QD_GROUP_3 - quasi-dynamic group 3 register 
  // QD_GROUP_4 - quasi-dynamic group 4 register 
  //------------------------------------------------------------------------------
  typedef enum bit [1:0]
  	{
  		QD_GROUP_1 =2'b00,
      QD_GROUP_2 =2'b01,
      QD_GROUP_3 =2'b10,
      QD_GROUP_4 =2'b11
  	} qd_group_e;

  //------------------------------------------------------------------------------
  // Enum: write_combine_state_e
  //------------------------------------------------------------------------------
  //  This is used to select <write_combine_state> from Write CAM.
  //------------------------------------------------------------------------------
  
  typedef enum logic [1:0] {
    IDLE    = 2'b00,
    COMBINE = 2'b01,
    BUFFER  = 2'b10,
    FLUSH   = 2'b11
  } write_combine_state_e;

	typedef enum bit [2:0] {
					                INIT = 3'b000,
					                NORMAL = 3'b001,
													POWER_DOWN = 3'b010,
													SELF_REFRESH = 3'b011//self_refresh or self_refresh power down
									       }lpddr_op_mode_e;

	typedef enum bit [2:0] {
					                NOT_IN_SELFREF = 3'b000,
													SELF_REF1 = 3'b001,
													SELFREF_POWERDOWN = 3'b010,
													SELF_REF2 = 3'b011,
													DEEP_SLEEP = 3'b100
									       }selfref_state_e;

typedef enum bit [1:0] {SR_POWERDOWN = 2'b00, //sr-powerdown
					                AUTOMATIC_SELFREF = 2'b11,//selfref caused by  automatic self refresh
													OTHER_SELFREF = 2'b10,//selfref caused by harware low power interface or software
													PHY_MASTER_REQUEST = 2'b01//selfref caused by phy master or normal ppt2
									       }selfref_type_e;

endpackage : lpddr_subsystem_typedef_pkg

`endif //LPDDR_SUBSYSTEM_TYPEDEF_PKG_SV
