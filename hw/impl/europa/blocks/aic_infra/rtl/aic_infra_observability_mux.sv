// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owners:
// - Pascal Hager <Pascal.Hager@axelera.ai>
// - Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

// Switch the observability signals for the ai_core europa implementation
//
module aic_infra_observability_mux (
  input wire i_clk,
  input wire i_rst_n,

  input aic_csr_reg_pkg::aic_csr_reg2hw_obs_ctrl_reg_t i_obs_ctrl,
  input aic_csr_reg_pkg::aic_csr_reg2hw_obs_rearange_mreg_t [aic_common_pkg::AIC_OBS_DW-1:0] i_obs_rearange,

  input aic_csr_reg_pkg::aic_csr_reg2hw_sw_obs_reg_t   i_sw_obs,
  input  aic_common_pkg::aic_dev_obs_t                 i_mvm_exe_obs,
  input  aic_common_pkg::aic_dev_obs_t                 i_mvm_prg_obs,
  input  aic_common_pkg::aic_dev_obs_t                 i_m_iau_obs,
  input  aic_common_pkg::aic_dev_obs_t                 i_m_dpu_obs,
  input  aic_common_pkg::tu_obs_t                      i_tu_obs,
  input  aic_common_pkg::aic_dev_obs_t                 i_dwpu_obs,
  input  aic_common_pkg::aic_dev_obs_t                 i_d_iau_obs,
  input  aic_common_pkg::aic_dev_obs_t                 i_d_dpu_obs,
  input  aic_common_pkg::dmc_obs_t                     i_dmc_obs,
  input  dma_pkg::dma_dev_obs_t                        i_dma_0_obs,
  input  dma_pkg::dma_dev_obs_t                        i_dma_1_obs,

  output logic [aic_common_pkg::AIC_OBS_DW-1:0]        o_aic_obs,
  output aic_csr_reg_pkg::aic_csr_hw2reg_obs_sig_reg_t o_sw_obs_rd
);

  localparam int unsigned SwObsWidth = $bits(aic_csr_reg_pkg::aic_csr_hw2reg_obs_sig_reg_t);

  // IO registers
  logic [aic_common_pkg::AIC_OBS_DW-1:0]  obs_mux, obs_mux_q, obs_rearanged, obs_rearanged_q;
  logic obs_en, obs_en_q;

  aic_csr_reg_pkg::aic_csr_hw2reg_obs_sig_reg_t sw_obs_rd, sw_obs_rd_q;
  logic sw_obs_rd_en;

  always_comb obs_en = (obs_mux != obs_mux_q);
  always_comb o_aic_obs = obs_rearanged_q;
  always_comb sw_obs_rd_en = (sw_obs_rd != sw_obs_rd_q);
  always_comb o_sw_obs_rd = sw_obs_rd_q;

  // MUX
  always_comb begin
    obs_mux = '0;
    unique case (i_obs_ctrl.q)
      aic_infra_pkg::OBS_SW:
          obs_mux = i_sw_obs;
      aic_infra_pkg::OBS_IDLE:
          begin
            obs_mux[0] = i_dmc_obs.m_ifd0_obs.state == cmdblock_pkg::idle;
            obs_mux[1] = i_dmc_obs.m_ifd1_obs.state == cmdblock_pkg::idle;
            obs_mux[2] = i_dmc_obs.m_ifd2_obs.state == cmdblock_pkg::idle;
            obs_mux[3] = i_dmc_obs.m_ifdw_obs.state == cmdblock_pkg::idle;
            obs_mux[4] = i_dmc_obs.m_odr_obs.state == cmdblock_pkg::idle;
            obs_mux[5] = i_dmc_obs.d_ifd0_obs.state == cmdblock_pkg::idle;
            obs_mux[6] = i_dmc_obs.d_ifd1_obs.state == cmdblock_pkg::idle;
            obs_mux[7] = i_dmc_obs.d_odr_obs.state == cmdblock_pkg::idle;
            obs_mux[8] = i_mvm_exe_obs.state == cmdblock_pkg::idle;
            obs_mux[9] = i_mvm_prg_obs.state == cmdblock_pkg::idle;
            obs_mux[10] = i_m_iau_obs.state == cmdblock_pkg::idle;
            obs_mux[11] = i_m_dpu_obs.state == cmdblock_pkg::idle;
            obs_mux[12] = i_dwpu_obs.state == cmdblock_pkg::idle;
            obs_mux[13] = i_d_iau_obs.state == cmdblock_pkg::idle;
            obs_mux[14] = i_d_dpu_obs.state == cmdblock_pkg::idle;
            obs_mux[15] = (i_dma_0_obs.state == cmdblock_pkg::idle) && (i_dma_1_obs.state == cmdblock_pkg::idle);
          end
      aic_infra_pkg::OBS_BUSY:
          begin
            obs_mux[0] = i_dmc_obs.m_ifd0_obs.state == cmdblock_pkg::exec;
            obs_mux[1] = i_dmc_obs.m_ifd1_obs.state == cmdblock_pkg::exec;
            obs_mux[2] = i_dmc_obs.m_ifd2_obs.state == cmdblock_pkg::exec;
            obs_mux[3] = i_dmc_obs.m_ifdw_obs.state == cmdblock_pkg::exec;
            obs_mux[4] = i_dmc_obs.m_odr_obs.state == cmdblock_pkg::exec;
            obs_mux[5] = i_dmc_obs.d_ifd0_obs.state == cmdblock_pkg::exec;
            obs_mux[6] = i_dmc_obs.d_ifd1_obs.state == cmdblock_pkg::exec;
            obs_mux[7] = i_dmc_obs.d_odr_obs.state == cmdblock_pkg::exec;
            obs_mux[8] = i_mvm_exe_obs.state == cmdblock_pkg::exec;
            obs_mux[9] = i_mvm_prg_obs.state == cmdblock_pkg::exec;
            obs_mux[10] = i_m_iau_obs.state == cmdblock_pkg::exec;
            obs_mux[11] = i_m_dpu_obs.state == cmdblock_pkg::exec;
            obs_mux[12] = i_dwpu_obs.state == cmdblock_pkg::exec;
            obs_mux[13] = i_d_iau_obs.state == cmdblock_pkg::exec;
            obs_mux[14] = i_d_dpu_obs.state == cmdblock_pkg::exec;
            obs_mux[15] = (i_dma_0_obs.state == cmdblock_pkg::exec) || (i_dma_1_obs.state == cmdblock_pkg::exec);
          end
      aic_infra_pkg::OBS_ACTIVITY:
          begin
            obs_mux[0] = i_sw_obs[0];
            obs_mux[1] = i_dmc_obs.m_ifd0_obs.state == cmdblock_pkg::exec;
            obs_mux[2] = i_dmc_obs.m_ifd1_obs.state == cmdblock_pkg::exec;
            obs_mux[3] = i_dmc_obs.m_ifd2_obs.state == cmdblock_pkg::exec;
            obs_mux[4] = i_mvm_exe_obs.state == cmdblock_pkg::exec;
            obs_mux[5] = i_dmc_obs.m_odr_obs.state == cmdblock_pkg::exec;
            obs_mux[6] = i_dmc_obs.m_ifdw_obs.state == cmdblock_pkg::exec;
            obs_mux[7] = i_mvm_prg_obs.state == cmdblock_pkg::exec;
            obs_mux[8] = i_dmc_obs.d_ifd0_obs.state == cmdblock_pkg::exec;
            obs_mux[9] = i_dmc_obs.d_ifd1_obs.state == cmdblock_pkg::exec;
            obs_mux[10] = i_dwpu_obs.state == cmdblock_pkg::exec;
            obs_mux[11] = i_dmc_obs.d_odr_obs.state == cmdblock_pkg::exec;
            obs_mux[12] = i_dma_0_obs.state == cmdblock_pkg::exec;
            obs_mux[13] = i_dma_1_obs.state == cmdblock_pkg::exec;
            obs_mux[15:14] = i_tu_obs[14:13];
          end
      aic_infra_pkg::OBS_THROTTLE:
          begin
            obs_mux[0] = i_sw_obs[0];
            obs_mux[15:1] = i_tu_obs[14:0];
          end
      default:  obs_mux = i_sw_obs;
    endcase
  end

  always_comb begin
    for (int unsigned i=0; i<aic_common_pkg::AIC_OBS_DW; i++)
      obs_rearanged[i] = obs_mux_q[i_obs_rearange[i]];
  end

  // SW OBS assigment, these go directly to CSR register
  always_comb begin
    sw_obs_rd = '0;
    sw_obs_rd.mvmexe_state.d      = i_mvm_exe_obs.state;
    sw_obs_rd.mvmprg_state.d      = i_mvm_prg_obs.state;
    sw_obs_rd.m_iau_state.d       = i_m_iau_obs.state;
    sw_obs_rd.m_dpu_state.d       = i_m_dpu_obs.state;
    sw_obs_rd.d_dwpu_state.d      = i_dwpu_obs.state;
    sw_obs_rd.d_iau_state.d       = i_d_iau_obs.state;
    sw_obs_rd.d_dpu_state.d       = i_d_dpu_obs.state;
    sw_obs_rd.m_idf0_state.d  = i_dmc_obs.m_ifd0_obs.state;
    sw_obs_rd.m_idf1_state.d  = i_dmc_obs.m_ifd1_obs.state;
    sw_obs_rd.m_idf2_state.d  = i_dmc_obs.m_ifd2_obs.state;
    sw_obs_rd.m_idfw_state.d  = i_dmc_obs.m_ifdw_obs.state;
    sw_obs_rd.m_odr_state.d   = i_dmc_obs.m_odr_obs.state;
    sw_obs_rd.d_idf0_state.d  = i_dmc_obs.d_ifd0_obs.state;
    sw_obs_rd.d_idf1_state.d  = i_dmc_obs.d_ifd1_obs.state;
    sw_obs_rd.d_odr_state.d   = i_dmc_obs.d_odr_obs.state;
    sw_obs_rd.tu_obs.d        = i_tu_obs;
  end

  //////////////////////////
  // Flops to break paths //
  //////////////////////////

  // DFFR: D-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      obs_mux_q <= '0;
      obs_rearanged_q <= '0;
      obs_en_q <= '0;
      sw_obs_rd_q <= '0;
    end else begin
      if (obs_en) obs_mux_q <= obs_mux;
      if (obs_en_q) obs_rearanged_q <= obs_rearanged;
      if (sw_obs_rd_en) sw_obs_rd_q <= sw_obs_rd;

      if(obs_en | obs_en_q) obs_en_q <= obs_en;
    end
  end

endmodule
