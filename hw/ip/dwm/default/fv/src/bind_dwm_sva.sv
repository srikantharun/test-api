// (C) Copyright 2025 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

/// Bind SVA in dwm
///

//bind dwm dwm_sva u_dwm_sva (.*);
bind dwm_observation_reader dwm_observation_reader_sva #(
  .ENABLE_ASSERT (1'b1),
  .ENABLE_ASSUME (1'b1),
  .ENABLE_COVER  (1'b1),
  .OVERCONSTRAINT(1'b0),
  .N_OBS         (N_OBS),
  .data_t        (data_t)
  ) u_dwm_observation_reader_sva (.*);

bind dwm_boost_requester dwm_boost_requester_sva #(
  .ENABLE_ASSERT (1'b1),
  .ENABLE_ASSUME (1'b1),
  .ENABLE_COVER  (1'b1),
  .OVERCONSTRAINT(1'b0),
  .data_t        (data_t)
  ) u_dwm_boost_requester_sva (.*);
