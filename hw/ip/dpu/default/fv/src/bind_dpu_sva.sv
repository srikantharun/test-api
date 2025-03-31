// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>

/// Bind SVA in dpu
///

bind dpu_dp_fp16_to_fp18 dpu_dp_fp_to_fp_sva #(.inp_t(fp16_t), .oup_t(dpu_fp_t)) u_fp_to_fp_sva (.*);
bind dpu_dp_fp18_to_fp16 dpu_dp_fp_to_fp_sva #(.inp_t(dpu_fp_t), .oup_t(fp16_t)) u_fp_to_fp_sva (.*);
bind dpu_dp_fp18_to_fp32 dpu_dp_fp_to_fp_sva #(.inp_t(dpu_fp_t), .oup_t(fp32_t)) u_fp_to_fp_sva (.*);
bind dpu_dp_fp32_to_fp18 dpu_dp_fp_to_fp_sva #(.inp_t(fp32_t), .oup_t(dpu_fp_t)) u_fp_to_fp_sva (.*);
