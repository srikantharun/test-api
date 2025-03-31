// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS Token Manager Connection.
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

// Macros for assigning TOKEN MANAGER if connections

`define assign_dmc_token_manager_if(index, conn_name, conn_param) \
  /* PRODUCERS */ \
  for (genvar i=0; i < TOK_MGR_``conn_param``_NR_TOK_PROD; i++) begin \
    assign m_dmc_token_if[index][i].reset_n      = axi_reset_if.reset; \
    assign m_dmc_token_if[index][i].tok_prod_vld = o_``conn_name``_tok_prod_vld[i]; \
    //assign `LS_DUT_PATH.i_``conn_name``_tok_prod_rdy[i] = m_dmc_token_if[index][i].tok_prod_rdy; \
    assign i_``conn_name``_tok_prod_rdy[i] = '1; \
  end \
  /* CONSUMERS */ \
  for (genvar i=0; i < TOK_MGR_``conn_param``_NR_TOK_CONS; i++) begin \
    //assign `LS_DUT_PATH.i_``conn_name``_tok_cons_vld[i] = m_dmc_token_if[index][i].tok_cons_vld; \
    assign i_``conn_name``_tok_cons_vld[i] = '1; \
    assign m_dmc_token_if[index][i].tok_cons_rdy = o_``conn_name``_tok_cons_rdy; \
  end

import token_mgr_mapping_aic_pkg::*;

parameter string TOKEN_VECTOR_DMC_CONNECTIONS[8] = {"m_ifd0", "m_ifd1", "m_ifd2", "m_ifdw", "m_odr", "d_ifd0", "d_ifd1", "d_odr"};
parameter string TOKEN_VECTOR_OTHER_CONNECTIONS[3] = {"sw", "hp_dma_0", "hp_dma_1"};

// IFD ODR Connections, in the following order: m_ifd0, m_ifd1, m_ifd2, m_ifdw, m_odr, d_ifd0, d_ifd1, d_odr
token_agent_if  m_dmc_token_if[8][11] (`LS_DUT_PATH.i_clk);

`assign_dmc_token_manager_if(0, m_ifd0, M_IFD_0)
`assign_dmc_token_manager_if(1, m_ifd1, M_IFD_1)
`assign_dmc_token_manager_if(2, m_ifd2, M_IFD_2)
`assign_dmc_token_manager_if(3, m_ifdw, M_IFD_W)
`assign_dmc_token_manager_if(4, m_odr, M_ODR)
`assign_dmc_token_manager_if(5, d_ifd0, D_IFD_0)
`assign_dmc_token_manager_if(6, d_ifd1, D_IFD_1)
`assign_dmc_token_manager_if(7, d_odr, D_ODR)


// we need to create token agent for each connection - all IFDs/ODRs to everything else!
for (genvar i=0; i<8; i++) begin //going through all IFDs/ODRs
  initial uvm_config_db#(virtual token_agent_if)::set(null, $sformatf("%s.tkn_%s_to_%s",LS_ENV_PATH, TOKEN_VECTOR_DMC_CONNECTIONS[i], TOKEN_VECTOR_OTHER_CONNECTIONS[0]), "vif", m_dmc_token_if[i][0]); // connection to sw
  for(genvar j=0; j<8+2; j++) begin
    initial begin
      if (j > 7) begin
        uvm_config_db#(virtual token_agent_if)::set(null, $sformatf("%s.tkn_%s_to_%s",LS_ENV_PATH, TOKEN_VECTOR_DMC_CONNECTIONS[i], TOKEN_VECTOR_OTHER_CONNECTIONS[(j+1)-8]), "vif", m_dmc_token_if[i][j]);
      end else if (j > i) begin
        uvm_config_db#(virtual token_agent_if)::set(null, $sformatf("%s.tkn_%s_to_%s",LS_ENV_PATH, TOKEN_VECTOR_DMC_CONNECTIONS[i], TOKEN_VECTOR_DMC_CONNECTIONS[j]), "vif", m_dmc_token_if[i][j]);
      end else if (j < i) begin
        uvm_config_db#(virtual token_agent_if)::set(null, $sformatf("%s.tkn_%s_to_%s",LS_ENV_PATH, TOKEN_VECTOR_DMC_CONNECTIONS[i], TOKEN_VECTOR_DMC_CONNECTIONS[j]), "vif", m_dmc_token_if[i][j+1]);
      end
    end
  end
end
