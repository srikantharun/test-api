// Description: Header file for AI core layer normalization kernel
// Owner: Michael Platzer <michael.platzer@axelera.ai>

#pragma once

#include <stdint.h>
#include <dlpack.h>
#include <dlpack_util.h>

/**
 * Standard-score layer normalization kernel, as specified in
 * https://axeleraai.atlassian.net/wiki/spaces/archrd/pages/342556677/Kernel+Reference#Kernel-Table
 *
 * This function applies standard-score normalization (i.e., subtracting the mean and dividing by
 * the standard deviation) to an n-dimensional tensor.  The normalization is performed over the
 * entire sub-tensors of dimensions `axis` through n - 1.
 *
 * Standard-score normalization is the normalization function typically used for normalization
 * layers in neuronal networks (e.g., refer to the various normalization layers in the PyTorch
 * documentation https://pytorch.org/docs/stable/nn.html#normalization-layers).
 *
 * All input and output tensors must in IEEE 754 half precision floating-point format (fp16).  The
 * values are internally cast to single precision floating-point format (fp32) before performing
 * any computations and the output tensor values are converted back to fp16 before storing.
 *
 * When computing the standard deviation, a stabilization term is optionally added to the variance
 * before taking the square root for numerical stability.  The normalized result is multiplied by a
 * scale tensor and a bias tensor is added to it, both of which have a shape equal to the sub-
 * tensors over which the normalization is performed.
 *
 * @param[out] Y       Output data tensor with n dimensions, e.g. [N, H, W, C].
 * @param[in]  X       Input data tensor with identical shape as Y, e.g. [N, H, W, C].
 * @param[in]  Scale   Tensor of scaling values with shape equal to the normalized shape, e.g. [C].
 * @param[in]  B       Tensor of bias values with shape equal to the normalized shape, e.g. [C].
 * @param[in]  axis    First normalization dimension (i.e., the normalization is performed over
 *                     dimensions `axis` through n - 1 of X), e.g. 3.
 * @param[in]  epsilon Stabilization term which is added to the variance for numerical stability.
 */
void kernel_aic_layernorm_fp(DLTensor *Y, const DLTensor *X, const DLTensor *Scale, const DLTensor *B, int8_t axis,
                             _Float16 epsilon);
