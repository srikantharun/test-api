// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: axi fabric external decoder parameters, Generated based on fabric_slave.hjson
// Owner: Luyi <yi.lu@axelera.ai>

`ifndef AIC_FABRIC_PKG_SV
`define AIC_FABRIC_PKG_SV

package aic_fabric_pkg;
  import aipu_addr_map_pkg::*;
  import aic_addr_map_pkg::*;
  import aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH;
  import aic_common_pkg::AIC_CID_LSB;
  import aic_common_pkg::AIC_CID_WIDTH;

  parameter int AIC_FABRIC_CORE_ID_LSB = AIC_CID_LSB;
  parameter int AIC_FABRIC_CORE_ID_W = AIC_CID_WIDTH;
  parameter int AIC_FABRIC_NUM_CORE = 8;
  parameter int AIC_FABRIC_CORE_ID[AIC_FABRIC_NUM_CORE] = {1, 2, 3, 4, 5, 6, 7, 8};
  parameter int AIC_FABRIC_AXI_AW = AIC_LT_AXI_ADDR_WIDTH;

  // external decoder related paras

%for item in BUS:
  // ${item}
  // default
  parameter int AIC_FABRIC_${item}_NUM_SLAVES = ${BUS[item]["slave_num"]};
  parameter int AIC_FABRIC_${item}_NUM_MASTERS = ${BUS[item]["master_num"]};

  parameter int AIC_FABRIC_${item}_NUM_ADDR_REGION = ${BUS[item]["regionNum"]};
  parameter longint AIC_FABRIC_${item}_ADDR_S[AIC_FABRIC_${item}_NUM_ADDR_REGION] = {

  %for i, key in enumerate(BUS[item]["postMap"]):
    %if i > 0:
    ,
    %endif
    %for idx in range(len(BUS[item]["postMap"][key]["name"])):
      %if idx > 0:
    ,
      %endif
    ${BUS[item]["postMap"][key]["name"][idx][0]}
  %endfor
  %endfor
  };

  parameter longint AIC_FABRIC_${item}_ADDR_E[AIC_FABRIC_${item}_NUM_ADDR_REGION] = {
  %for i, key in enumerate(BUS[item]["postMap"]):
    %if i > 0:
    ,
    %endif
    %for idx in range(len(BUS[item]["postMap"][key]["name"])):
      %if idx > 0:
    ,
      %endif
    ${BUS[item]["postMap"][key]["name"][idx][1]}
    %endfor
  %endfor
  };

  parameter bit AIC_FABRIC_${item}_REGION_IS_CORE[AIC_FABRIC_${item}_NUM_ADDR_REGION] = {
  %for i, key in enumerate(BUS[item]["postMap"]):
    %if i > 0:
    ,
    %endif
    %for idx in range(len(BUS[item]["postMap"][key]["name"])):
      %if idx > 0:
    ,
      %endif
      %if BUS[item]["postMap"][key]["name"][idx][0].startswith("AIC_") or BUS[item]["postMap"][key]["name"][idx][0].startswith("AICORE_0_"):
    1
      %else:
    0
      %endif
    %endfor
  %endfor
  };

  parameter int AIC_FABRIC_${item}_DEFAULT_SLAVE = ${BUS[item]["inDefault"]};
  parameter int AIC_FABRIC_${item}_NOT_THIS_CORE_SLAVE = ${BUS[item]["outDefault"]};

  parameter int AIC_FABRIC_${item}_SL_IDX[AIC_FABRIC_${item}_NUM_ADDR_REGION] = {
  %for i, key in enumerate(BUS[item]["postMap"]):
    %if i > 0:
    ,
    %endif
    %for idx in range(len(BUS[item]["postMap"][key]["name"])):
      %if idx > 0:
    ,
      %endif
      ${key}
    %endfor
  %endfor
  };
%endfor

endpackage

`endif // AIC_FABRIC_PKG_SV
