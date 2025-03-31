// Description: Attention kernel
// Owner: Michael Platzer <michael.platzer@axelera.ai>

#include <attention.h>
#include <riscv_vector.h>
#include <math.h>
#include <rvv_math.h>
#include <printf.h>

////////////
// Scalar //
////////////

void attention(uint32_t Nxh, uint32_t S, uint32_t L, uint32_t d_k, _Float16 inv_sqrt_d_k, const _Float16 *Q,
               const _Float16 *K, const _Float16 *V, _Float16 *QK, _Float16 *A) {
  for (uint32_t i = 0; i < Nxh; ++i) {
    for (uint32_t j = 0; j < S; ++j) {
      // multiply Q with K^T, divide by sqrt(d_k), and generate the softmax sum
      _Float16 sum = 0.0f;
      for (uint32_t k = 0; k < L; ++k) {
        QK[(i * S + j) * L + k] = 0.0f;
        for (uint32_t l = 0; l < d_k; ++l) {
          QK[(i * S + j) * L + k] += Q[(i * d_k + l) * S + j] * K[(i * d_k + l) * L + k];
        }
        QK[(i * S + j) * L + k] = expf((float)QK[(i * S + j) * L + k] * (float)inv_sqrt_d_k);
        sum                     += QK[(i * S + j) * L + k];
      }

      // divide the intermediate values by the softmax sum and multiply with V
      _Float16 sum_inv = (_Float16)(1.0f / (float)sum);
      for (uint32_t l = 0; l < d_k; ++l) {
        A[(i * d_k + l) * S + j] = 0.0f;
        for (uint32_t k = 0; k < L; ++k) {
          A[(i * d_k + l) * S + j] += (QK[(i * S + j) * L + k] * sum_inv) * V[(i * d_k + l) * L + k];
        }
      }
    }
  }
}

/////////
// RVV //
/////////

void attention_rvv(uint32_t Nxh, uint32_t S, uint32_t L, uint32_t d_k, _Float16 inv_sqrt_d_k, const _Float16 *Q,
                   const _Float16 *K, const _Float16 *V, _Float16 *QK, _Float16 *A) {
  // Vectorize over the Nxh dimension
  // Motivation: in LLM transformers:
  //  - the head count is typically between 32 and 128
  //  - the sequence length during inference starts at 1 and increments by 1 for every new token
  //  - the embedding size is typically around 1K (up to 4K for larger models)
  // Therefore, we expect:
  //  - Nxh to be at least 32
  //  - S to be either 1 or equal to L (1 for encoder/decoder attention, L for self-attention)
  //  - L to start at 1 and increment at every step (L is the sequence length)
  //  - d_k to be close to 32 (d_k is the query size, which is embedding size / head count)
  // Hence, Nxh is potentially the largest dimension (particularly for N > 1) and it is also the
  // easiest to vectorize, since all operations are simply element-wise, which allows us to retain
  // the structure of the scalar code.
  uint32_t vl;
  for (uint32_t i = 0; i < Nxh; i += vl) {
    vl = __riscv_vsetvl_e16m1(Nxh - i);

    uint32_t j = 0;
    // CAREFUL: heavily optimized version for S >= 4 making use of segment loads/stores;
    // collapse the following loop to see the simple un-optimized version
    for (; j + 4 <= S; j += 4) {
      // multiply Q with K^T, divide by sqrt(d_k), and generate the softmax sum
      vfloat16m1_t vsum0 = __riscv_vfmv_v_f_f16m1(0.0f, vl), vsum1 = __riscv_vfmv_v_f_f16m1(0.0f, vl),
                   vsum2 = __riscv_vfmv_v_f_f16m1(0.0f, vl), vsum3 = __riscv_vfmv_v_f_f16m1(0.0f, vl);
      uint32_t k = 0;
      for (; k + 4 <= L; k += 4) {
        vfloat16m1_t vq0k0 = __riscv_vfmv_v_f_f16m1(0.0f, vl), vq1k0 = __riscv_vfmv_v_f_f16m1(0.0f, vl),
                     vq0k1 = __riscv_vfmv_v_f_f16m1(0.0f, vl), vq1k1 = __riscv_vfmv_v_f_f16m1(0.0f, vl),
                     vq0k2 = __riscv_vfmv_v_f_f16m1(0.0f, vl), vq1k2 = __riscv_vfmv_v_f_f16m1(0.0f, vl),
                     vq0k3 = __riscv_vfmv_v_f_f16m1(0.0f, vl), vq1k3 = __riscv_vfmv_v_f_f16m1(0.0f, vl),
                     vq2k0 = __riscv_vfmv_v_f_f16m1(0.0f, vl), vq3k0 = __riscv_vfmv_v_f_f16m1(0.0f, vl),
                     vq2k1 = __riscv_vfmv_v_f_f16m1(0.0f, vl), vq3k1 = __riscv_vfmv_v_f_f16m1(0.0f, vl),
                     vq2k2 = __riscv_vfmv_v_f_f16m1(0.0f, vl), vq3k2 = __riscv_vfmv_v_f_f16m1(0.0f, vl),
                     vq2k3 = __riscv_vfmv_v_f_f16m1(0.0f, vl), vq3k3 = __riscv_vfmv_v_f_f16m1(0.0f, vl);
        for (uint32_t l = 0; l < d_k; ++l) {
          vfloat16m1x4_t vq = __riscv_vlsseg4e16_v_f16m1x4(Q + (i * d_k + l) * S + j, d_k * S * sizeof(_Float16), vl),
                         vk = __riscv_vlsseg4e16_v_f16m1x4(K + (i * d_k + l) * L + k, d_k * L * sizeof(_Float16), vl);
          vfloat16m1_t vq0 = __riscv_vget_v_f16m1x4_f16m1(vq, 0), vq1 = __riscv_vget_v_f16m1x4_f16m1(vq, 1),
                       vq2 = __riscv_vget_v_f16m1x4_f16m1(vq, 2), vq3 = __riscv_vget_v_f16m1x4_f16m1(vq, 3),
                       vk0 = __riscv_vget_v_f16m1x4_f16m1(vk, 0), vk1 = __riscv_vget_v_f16m1x4_f16m1(vk, 1),
                       vk2 = __riscv_vget_v_f16m1x4_f16m1(vk, 2), vk3 = __riscv_vget_v_f16m1x4_f16m1(vk, 3);
          vq0k0 = __riscv_vfmacc_vv_f16m1(vq0k0, vq0, vk0, vl);
          vq1k0 = __riscv_vfmacc_vv_f16m1(vq1k0, vq1, vk0, vl);
          vq0k1 = __riscv_vfmacc_vv_f16m1(vq0k1, vq0, vk1, vl);
          vq1k1 = __riscv_vfmacc_vv_f16m1(vq1k1, vq1, vk1, vl);
          vq0k2 = __riscv_vfmacc_vv_f16m1(vq0k2, vq0, vk2, vl);
          vq1k2 = __riscv_vfmacc_vv_f16m1(vq1k2, vq1, vk2, vl);
          vq0k3 = __riscv_vfmacc_vv_f16m1(vq0k3, vq0, vk3, vl);
          vq1k3 = __riscv_vfmacc_vv_f16m1(vq1k3, vq1, vk3, vl);
          vq2k0 = __riscv_vfmacc_vv_f16m1(vq2k0, vq2, vk0, vl);
          vq3k0 = __riscv_vfmacc_vv_f16m1(vq3k0, vq3, vk0, vl);
          vq2k1 = __riscv_vfmacc_vv_f16m1(vq2k1, vq2, vk1, vl);
          vq3k1 = __riscv_vfmacc_vv_f16m1(vq3k1, vq3, vk1, vl);
          vq2k2 = __riscv_vfmacc_vv_f16m1(vq2k2, vq2, vk2, vl);
          vq3k2 = __riscv_vfmacc_vv_f16m1(vq3k2, vq3, vk2, vl);
          vq2k3 = __riscv_vfmacc_vv_f16m1(vq2k3, vq2, vk3, vl);
          vq3k3 = __riscv_vfmacc_vv_f16m1(vq3k3, vq3, vk3, vl);
        }
        vq0k0 = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vq0k0, inv_sqrt_d_k, vl), vl);
        vq0k1 = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vq0k1, inv_sqrt_d_k, vl), vl);
        vq0k2 = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vq0k2, inv_sqrt_d_k, vl), vl);
        vq0k3 = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vq0k3, inv_sqrt_d_k, vl), vl);
        vq1k0 = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vq1k0, inv_sqrt_d_k, vl), vl);
        vq1k1 = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vq1k1, inv_sqrt_d_k, vl), vl);
        vq1k2 = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vq1k2, inv_sqrt_d_k, vl), vl);
        vq1k3 = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vq1k3, inv_sqrt_d_k, vl), vl);
        vq2k0 = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vq2k0, inv_sqrt_d_k, vl), vl);
        vq2k1 = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vq2k1, inv_sqrt_d_k, vl), vl);
        vq2k2 = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vq2k2, inv_sqrt_d_k, vl), vl);
        vq2k3 = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vq2k3, inv_sqrt_d_k, vl), vl);
        vq3k0 = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vq3k0, inv_sqrt_d_k, vl), vl);
        vq3k1 = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vq3k1, inv_sqrt_d_k, vl), vl);
        vq3k2 = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vq3k2, inv_sqrt_d_k, vl), vl);
        vq3k3 = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vq3k3, inv_sqrt_d_k, vl), vl);
        vsum0 = __riscv_vfadd_vv_f16m1(vsum0, vq0k0, vl);
        vsum1 = __riscv_vfadd_vv_f16m1(vsum1, vq1k0, vl);
        vsum0 = __riscv_vfadd_vv_f16m1(vsum0, vq0k1, vl);
        vsum1 = __riscv_vfadd_vv_f16m1(vsum1, vq1k1, vl);
        vsum0 = __riscv_vfadd_vv_f16m1(vsum0, vq0k2, vl);
        vsum1 = __riscv_vfadd_vv_f16m1(vsum1, vq1k2, vl);
        vsum0 = __riscv_vfadd_vv_f16m1(vsum0, vq0k3, vl);
        vsum1 = __riscv_vfadd_vv_f16m1(vsum1, vq1k3, vl);
        vsum2 = __riscv_vfadd_vv_f16m1(vsum2, vq2k0, vl);
        vsum3 = __riscv_vfadd_vv_f16m1(vsum3, vq3k0, vl);
        vsum2 = __riscv_vfadd_vv_f16m1(vsum2, vq2k1, vl);
        vsum3 = __riscv_vfadd_vv_f16m1(vsum3, vq3k1, vl);
        vsum2 = __riscv_vfadd_vv_f16m1(vsum2, vq2k2, vl);
        vsum3 = __riscv_vfadd_vv_f16m1(vsum3, vq3k2, vl);
        vsum2 = __riscv_vfadd_vv_f16m1(vsum2, vq2k3, vl);
        vsum3 = __riscv_vfadd_vv_f16m1(vsum3, vq3k3, vl);
        // TODO replace with __riscv_vcreate_v_f16m1x4() when it becomes available
        vfloat16m1x4_t vq0k = __riscv_vundefined_f16m1x4(), vq1k = __riscv_vundefined_f16m1x4(),
                       vq2k = __riscv_vundefined_f16m1x4(), vq3k = __riscv_vundefined_f16m1x4();
        vq0k = __riscv_vset_v_f16m1_f16m1x4(vq0k, 0, vq0k0);
        vq0k = __riscv_vset_v_f16m1_f16m1x4(vq0k, 1, vq0k1);
        vq0k = __riscv_vset_v_f16m1_f16m1x4(vq0k, 2, vq0k2);
        vq0k = __riscv_vset_v_f16m1_f16m1x4(vq0k, 3, vq0k3);
        vq1k = __riscv_vset_v_f16m1_f16m1x4(vq1k, 0, vq1k0);
        vq1k = __riscv_vset_v_f16m1_f16m1x4(vq1k, 1, vq1k1);
        vq1k = __riscv_vset_v_f16m1_f16m1x4(vq1k, 2, vq1k2);
        vq1k = __riscv_vset_v_f16m1_f16m1x4(vq1k, 3, vq1k3);
        vq2k = __riscv_vset_v_f16m1_f16m1x4(vq2k, 0, vq2k0);
        vq2k = __riscv_vset_v_f16m1_f16m1x4(vq2k, 1, vq2k1);
        vq2k = __riscv_vset_v_f16m1_f16m1x4(vq2k, 2, vq2k2);
        vq2k = __riscv_vset_v_f16m1_f16m1x4(vq2k, 3, vq2k3);
        vq3k = __riscv_vset_v_f16m1_f16m1x4(vq3k, 0, vq3k0);
        vq3k = __riscv_vset_v_f16m1_f16m1x4(vq3k, 1, vq3k1);
        vq3k = __riscv_vset_v_f16m1_f16m1x4(vq3k, 2, vq3k2);
        vq3k = __riscv_vset_v_f16m1_f16m1x4(vq3k, 3, vq3k3);
        __riscv_vssseg4e16_v_f16m1x4(QK + (i * S + j) * L + k, S * L * sizeof(_Float16), vq0k, vl);
        __riscv_vssseg4e16_v_f16m1x4(QK + (i * S + j + 1) * L + k, S * L * sizeof(_Float16), vq1k, vl);
        __riscv_vssseg4e16_v_f16m1x4(QK + (i * S + j + 2) * L + k, S * L * sizeof(_Float16), vq2k, vl);
        __riscv_vssseg4e16_v_f16m1x4(QK + (i * S + j + 3) * L + k, S * L * sizeof(_Float16), vq3k, vl);
      }
      for (; k < L; ++k) {
        vfloat16m1_t vq0k = __riscv_vfmv_v_f_f16m1(0.0f, vl), vq1k = __riscv_vfmv_v_f_f16m1(0.0f, vl),
                     vq2k = __riscv_vfmv_v_f_f16m1(0.0f, vl), vq3k = __riscv_vfmv_v_f_f16m1(0.0f, vl);
        for (uint32_t l = 0; l < d_k; ++l) {
          vfloat16m1x4_t vq = __riscv_vlsseg4e16_v_f16m1x4(Q + (i * d_k + l) * S + j, d_k * S * sizeof(_Float16), vl);
          vfloat16m1_t   vk = __riscv_vlse16_v_f16m1(K + (i * d_k + l) * L + k, d_k * L * sizeof(_Float16), vl);
          vq0k              = __riscv_vfmacc_vv_f16m1(vq0k, __riscv_vget_v_f16m1x4_f16m1(vq, 0), vk, vl);
          vq1k              = __riscv_vfmacc_vv_f16m1(vq1k, __riscv_vget_v_f16m1x4_f16m1(vq, 1), vk, vl);
          vq2k              = __riscv_vfmacc_vv_f16m1(vq2k, __riscv_vget_v_f16m1x4_f16m1(vq, 2), vk, vl);
          vq3k              = __riscv_vfmacc_vv_f16m1(vq3k, __riscv_vget_v_f16m1x4_f16m1(vq, 3), vk, vl);
        }
        vq0k  = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vq0k, inv_sqrt_d_k, vl), vl);
        vq1k  = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vq1k, inv_sqrt_d_k, vl), vl);
        vq2k  = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vq2k, inv_sqrt_d_k, vl), vl);
        vq3k  = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vq3k, inv_sqrt_d_k, vl), vl);
        vsum0 = __riscv_vfadd_vv_f16m1(vsum0, vq0k, vl);
        vsum1 = __riscv_vfadd_vv_f16m1(vsum1, vq1k, vl);
        vsum2 = __riscv_vfadd_vv_f16m1(vsum2, vq2k, vl);
        vsum3 = __riscv_vfadd_vv_f16m1(vsum3, vq3k, vl);
        __riscv_vsse16_v_f16m1(QK + (i * S + j) * L + k, S * L * sizeof(_Float16), vq0k, vl);
        __riscv_vsse16_v_f16m1(QK + (i * S + j + 1) * L + k, S * L * sizeof(_Float16), vq1k, vl);
        __riscv_vsse16_v_f16m1(QK + (i * S + j + 2) * L + k, S * L * sizeof(_Float16), vq2k, vl);
        __riscv_vsse16_v_f16m1(QK + (i * S + j + 3) * L + k, S * L * sizeof(_Float16), vq3k, vl);
      }

      // divide the intermediate values by the softmax sum and multiply with V
      // vfloat16m1_t vsum_inv = __riscv_vfrdiv_vf_f16m1(vsum, 1.f, vl);
      vfloat16m1_t vsum0_inv = __riscv_vfrec7_v_f16m1(vsum0, vl), vsum1_inv = __riscv_vfrec7_v_f16m1(vsum1, vl),
                   vsum2_inv = __riscv_vfrec7_v_f16m1(vsum2, vl), vsum3_inv = __riscv_vfrec7_v_f16m1(vsum3, vl);
      for (uint32_t l = 0; l < d_k; ++l) {
        vfloat16m1_t va0 = __riscv_vfmv_v_f_f16m1(0.0f, vl), va1 = __riscv_vfmv_v_f_f16m1(0.0f, vl),
                     va2 = __riscv_vfmv_v_f_f16m1(0.0f, vl), va3 = __riscv_vfmv_v_f_f16m1(0.0f, vl);
        uint32_t k = 0;
        for (; k + 4 <= L; k += 4) {
          vfloat16m1x4_t vq0k = __riscv_vlsseg4e16_v_f16m1x4(QK + (i * S + j) * L + k, S * L * sizeof(_Float16), vl),
                         vq1k =
                             __riscv_vlsseg4e16_v_f16m1x4(QK + (i * S + j + 1) * L + k, S * L * sizeof(_Float16), vl),
                         vq2k =
                             __riscv_vlsseg4e16_v_f16m1x4(QK + (i * S + j + 2) * L + k, S * L * sizeof(_Float16), vl),
                         vq3k =
                             __riscv_vlsseg4e16_v_f16m1x4(QK + (i * S + j + 3) * L + k, S * L * sizeof(_Float16), vl),
                         vv = __riscv_vlsseg4e16_v_f16m1x4(V + (i * d_k + l) * L + k, d_k * L * sizeof(_Float16), vl);
          vfloat16m1_t vv0 = __riscv_vget_v_f16m1x4_f16m1(vv, 0), vv1 = __riscv_vget_v_f16m1x4_f16m1(vv, 1),
                       vv2 = __riscv_vget_v_f16m1x4_f16m1(vv, 2), vv3 = __riscv_vget_v_f16m1x4_f16m1(vv, 3);
          va0 = __riscv_vfmacc_vv_f16m1(
              va0, __riscv_vfmul_vv_f16m1(__riscv_vget_v_f16m1x4_f16m1(vq0k, 0), vsum0_inv, vl), vv0, vl);
          va1 = __riscv_vfmacc_vv_f16m1(
              va1, __riscv_vfmul_vv_f16m1(__riscv_vget_v_f16m1x4_f16m1(vq1k, 0), vsum1_inv, vl), vv0, vl);
          va2 = __riscv_vfmacc_vv_f16m1(
              va2, __riscv_vfmul_vv_f16m1(__riscv_vget_v_f16m1x4_f16m1(vq2k, 0), vsum2_inv, vl), vv0, vl);
          va3 = __riscv_vfmacc_vv_f16m1(
              va3, __riscv_vfmul_vv_f16m1(__riscv_vget_v_f16m1x4_f16m1(vq3k, 0), vsum3_inv, vl), vv0, vl);
          va0 = __riscv_vfmacc_vv_f16m1(
              va0, __riscv_vfmul_vv_f16m1(__riscv_vget_v_f16m1x4_f16m1(vq0k, 1), vsum0_inv, vl), vv1, vl);
          va1 = __riscv_vfmacc_vv_f16m1(
              va1, __riscv_vfmul_vv_f16m1(__riscv_vget_v_f16m1x4_f16m1(vq1k, 1), vsum1_inv, vl), vv1, vl);
          va2 = __riscv_vfmacc_vv_f16m1(
              va2, __riscv_vfmul_vv_f16m1(__riscv_vget_v_f16m1x4_f16m1(vq2k, 1), vsum2_inv, vl), vv1, vl);
          va3 = __riscv_vfmacc_vv_f16m1(
              va3, __riscv_vfmul_vv_f16m1(__riscv_vget_v_f16m1x4_f16m1(vq3k, 1), vsum3_inv, vl), vv1, vl);
          va0 = __riscv_vfmacc_vv_f16m1(
              va0, __riscv_vfmul_vv_f16m1(__riscv_vget_v_f16m1x4_f16m1(vq0k, 2), vsum0_inv, vl), vv2, vl);
          va1 = __riscv_vfmacc_vv_f16m1(
              va1, __riscv_vfmul_vv_f16m1(__riscv_vget_v_f16m1x4_f16m1(vq1k, 2), vsum1_inv, vl), vv2, vl);
          va2 = __riscv_vfmacc_vv_f16m1(
              va2, __riscv_vfmul_vv_f16m1(__riscv_vget_v_f16m1x4_f16m1(vq2k, 2), vsum2_inv, vl), vv2, vl);
          va3 = __riscv_vfmacc_vv_f16m1(
              va3, __riscv_vfmul_vv_f16m1(__riscv_vget_v_f16m1x4_f16m1(vq3k, 2), vsum3_inv, vl), vv2, vl);
          va0 = __riscv_vfmacc_vv_f16m1(
              va0, __riscv_vfmul_vv_f16m1(__riscv_vget_v_f16m1x4_f16m1(vq0k, 3), vsum0_inv, vl), vv3, vl);
          va1 = __riscv_vfmacc_vv_f16m1(
              va1, __riscv_vfmul_vv_f16m1(__riscv_vget_v_f16m1x4_f16m1(vq1k, 3), vsum1_inv, vl), vv3, vl);
          va2 = __riscv_vfmacc_vv_f16m1(
              va2, __riscv_vfmul_vv_f16m1(__riscv_vget_v_f16m1x4_f16m1(vq2k, 3), vsum2_inv, vl), vv3, vl);
          va3 = __riscv_vfmacc_vv_f16m1(
              va3, __riscv_vfmul_vv_f16m1(__riscv_vget_v_f16m1x4_f16m1(vq3k, 3), vsum3_inv, vl), vv3, vl);
        }
        for (; k < L; ++k) {
          vfloat16m1_t vq0k = __riscv_vlse16_v_f16m1(QK + (i * S + j) * L + k, S * L * sizeof(_Float16), vl),
                       vq1k = __riscv_vlse16_v_f16m1(QK + (i * S + j + 1) * L + k, S * L * sizeof(_Float16), vl),
                       vq2k = __riscv_vlse16_v_f16m1(QK + (i * S + j + 2) * L + k, S * L * sizeof(_Float16), vl),
                       vq3k = __riscv_vlse16_v_f16m1(QK + (i * S + j + 3) * L + k, S * L * sizeof(_Float16), vl),
                       vv   = __riscv_vlse16_v_f16m1(V + (i * d_k + l) * L + k, d_k * L * sizeof(_Float16), vl);
          va0               = __riscv_vfmacc_vv_f16m1(va0, __riscv_vfmul_vv_f16m1(vq0k, vsum0_inv, vl), vv, vl);
          va1               = __riscv_vfmacc_vv_f16m1(va1, __riscv_vfmul_vv_f16m1(vq1k, vsum1_inv, vl), vv, vl);
          va2               = __riscv_vfmacc_vv_f16m1(va2, __riscv_vfmul_vv_f16m1(vq2k, vsum2_inv, vl), vv, vl);
          va3               = __riscv_vfmacc_vv_f16m1(va3, __riscv_vfmul_vv_f16m1(vq3k, vsum3_inv, vl), vv, vl);
        }
        // TODO replace with __riscv_vcreate_v_f16m1x4() when it becomes available
        // vfloat16m1x4_t va;
        vfloat16m1x4_t va = __riscv_vundefined_f16m1x4();
        va = __riscv_vset_v_f16m1_f16m1x4(va, 0, va0);
        va = __riscv_vset_v_f16m1_f16m1x4(va, 1, va1);
        va = __riscv_vset_v_f16m1_f16m1x4(va, 2, va2);
        va = __riscv_vset_v_f16m1_f16m1x4(va, 3, va3);
        __riscv_vssseg4e16_v_f16m1x4(A + (i * d_k + l) * S + j, d_k * S * sizeof(_Float16), va, vl);
      }
    }
    for (; j < S; ++j) {
      // multiply Q with K^T, divide by sqrt(d_k), and generate the softmax sum
      vfloat16m1_t vsum = __riscv_vfmv_v_f_f16m1(0.0f, vl);

      uint32_t k = 0;
      // Collapse the following loop as well to see a clean version ... good, that's better, right?
      for (; k + 4 <= L; k += 4) {
        vfloat16m1_t vqk0 = __riscv_vfmv_v_f_f16m1(0.0f, vl), vqk1 = __riscv_vfmv_v_f_f16m1(0.0f, vl),
                     vqk2 = __riscv_vfmv_v_f_f16m1(0.0f, vl), vqk3 = __riscv_vfmv_v_f_f16m1(0.0f, vl);
        for (uint32_t l = 0; l < d_k; ++l) {
          vfloat16m1x4_t vk = __riscv_vlsseg4e16_v_f16m1x4(K + (i * d_k + l) * L + k, d_k * L * sizeof(_Float16), vl);
          vfloat16m1_t   vq = __riscv_vlse16_v_f16m1(Q + (i * d_k + l) * S + j, d_k * S * sizeof(_Float16), vl);
          vqk0              = __riscv_vfmacc_vv_f16m1(vqk0, vq, __riscv_vget_v_f16m1x4_f16m1(vk, 0), vl);
          vqk1              = __riscv_vfmacc_vv_f16m1(vqk1, vq, __riscv_vget_v_f16m1x4_f16m1(vk, 1), vl);
          vqk2              = __riscv_vfmacc_vv_f16m1(vqk2, vq, __riscv_vget_v_f16m1x4_f16m1(vk, 2), vl);
          vqk3              = __riscv_vfmacc_vv_f16m1(vqk3, vq, __riscv_vget_v_f16m1x4_f16m1(vk, 3), vl);
        }
        vqk0 = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vqk0, inv_sqrt_d_k, vl), vl);
        vqk1 = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vqk1, inv_sqrt_d_k, vl), vl);
        vqk2 = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vqk2, inv_sqrt_d_k, vl), vl);
        vqk3 = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vqk3, inv_sqrt_d_k, vl), vl);
        vsum = __riscv_vfadd_vv_f16m1(vsum, vqk0, vl);
        vsum = __riscv_vfadd_vv_f16m1(vsum, vqk1, vl);
        vsum = __riscv_vfadd_vv_f16m1(vsum, vqk2, vl);
        vsum = __riscv_vfadd_vv_f16m1(vsum, vqk3, vl);
        // TODO replace with __riscv_vcreate_v_f16m1x4() when it becomes available
        vfloat16m1x4_t vqk = __riscv_vundefined_f16m1x4();
        vqk = __riscv_vset_v_f16m1_f16m1x4(vqk, 0, vqk0);
        vqk = __riscv_vset_v_f16m1_f16m1x4(vqk, 1, vqk1);
        vqk = __riscv_vset_v_f16m1_f16m1x4(vqk, 2, vqk2);
        vqk = __riscv_vset_v_f16m1_f16m1x4(vqk, 3, vqk3);
        __riscv_vssseg4e16_v_f16m1x4(QK + (i * S + j) * L + k, S * L * sizeof(_Float16), vqk, vl);
      }
      for (; k < L; ++k) {
        vfloat16m1_t vqk = __riscv_vfmv_v_f_f16m1(0.0f, vl);
        for (uint32_t l = 0; l < d_k; ++l) {
          vfloat16m1_t vq = __riscv_vlse16_v_f16m1(Q + (i * d_k + l) * S + j, d_k * S * sizeof(_Float16), vl),
                       vk = __riscv_vlse16_v_f16m1(K + (i * d_k + l) * L + k, d_k * L * sizeof(_Float16), vl);
          vqk             = __riscv_vfmacc_vv_f16m1(vqk, vq, vk, vl);
        }
        vqk  = exp_ps_f16m1(__riscv_vfmul_vf_f16m1(vqk, inv_sqrt_d_k, vl), vl);
        vsum = __riscv_vfadd_vv_f16m1(vsum, vqk, vl);
        __riscv_vsse16_v_f16m1(QK + (i * S + j) * L + k, S * L * sizeof(_Float16), vqk, vl);
      }

      // divide the intermediate values by the softmax sum and multiply with V
      // vfloat16m1_t vsum_inv = __riscv_vfrdiv_vf_f16m1(vsum, 1.f, vl);
      vfloat16m1_t vsum_inv = __riscv_vfrec7_v_f16m1(vsum, vl);
      for (uint32_t l = 0; l < d_k; ++l) {
        vfloat16m1_t va = __riscv_vfmv_v_f_f16m1(0.0f, vl);
        for (uint32_t k = 0; k < L; ++k) {
          vfloat16m1_t vqk = __riscv_vlse16_v_f16m1(QK + (i * S + j) * L + k, S * L * sizeof(_Float16), vl),
                       vv  = __riscv_vlse16_v_f16m1(V + (i * d_k + l) * L + k, d_k * L * sizeof(_Float16), vl);
          va               = __riscv_vfmacc_vv_f16m1(va, __riscv_vfmul_vv_f16m1(vqk, vsum_inv, vl), vv, vl);
        }
        // TODO replace with __riscv_vcreate_v_f16m1x4() when it becomes available
        __riscv_vsse16_v_f16m1(A + (i * d_k + l) * S + j, d_k * S * sizeof(_Float16), va, vl);
      }
    }
  }
}
