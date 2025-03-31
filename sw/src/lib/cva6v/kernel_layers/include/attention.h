// Description: Header file for attention kernel
// Owner: Michael Platzer <michael.platzer@axelera.ai>

#pragma once

#include <stdint.h>

/**
 * Scalar and vectorized variants of multi-head attention.
 *
 * Computes scaled dot-product attention, as defined by Vaswani et al. in equation (1) of "Attention
 * is all you need" (https://arxiv.org/pdf/1706.03762.pdf).
 *
 * @param Nxh          Batch size N times head count h (i.e., sample count for attention operation).
 * @param S            Encoder sequence length (for encoder/decoder attention, otherwise equals L).
 * @param L            Decoder sequence length.
 * @param d_k          Query size (typically embedding size / head count).
 * @param inv_sqrt_d_k Inverse square-root of d_k.
 * @param Q            Q matrix of the attention operation, shape [Nxh, d_k, S].
 * @param K            K matrix of the attention operation, shape [Nxh, d_k, L].
 * @param V            V matrix of the attention operation, shape [Nxh, d_k, L].
 * @param QK           Temporary buffer for the softmax input matrix, shape [Nxh, S, L].
 * @param A            Attention output matrix, shape [Nxh, d_k, S].
 */
void attention(uint32_t Nxh, uint32_t S, uint32_t L, uint32_t d_k, _Float16 inv_sqrt_d_k, const _Float16 *Q,
               const _Float16 *K, const _Float16 *V, _Float16 *QK, _Float16 *A);
void attention_rvv(uint32_t Nxh, uint32_t S, uint32_t L, uint32_t d_k, _Float16 inv_sqrt_d_k, const _Float16 *Q,
                   const _Float16 *K, const _Float16 *V, _Float16 *QK, _Float16 *A);
