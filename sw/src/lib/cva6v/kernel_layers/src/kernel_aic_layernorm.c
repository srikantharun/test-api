// Description: AI core layer normalization kernel
// Owner: Michael Platzer <michael.platzer@axelera.ai>

#include <kernel_aic_layernorm.h>
#include <math.h>
#include <riscv_vector.h>
#include <rvv_math.h>
#include <rvv_ops.h>

vfloat32m2_t   rvv_tensor_sum_f32m2(vfloat32m2_t vsum, const DLTensor *X);
vfloat32m2x2_t rvv_tensor_squared_diff_sum_f32m2(vfloat32m2_t vsum, const DLTensor *X, vfloat32m2_t sub);
vfloat32m2x2_t rvv_tensor_normalize(DLTensor *Y, const DLTensor *X, vfloat32m2_t vmean_neg, vfloat32m2_t vstd_inv,
                                    const DLTensor *Scale, const DLTensor *B);

void kernel_aic_layernorm_fp(DLTensor *Y, const DLTensor *X, const DLTensor *Scale, const DLTensor *B, int8_t axis,
                             _Float16 epsilon) {
  if (axis > 0) {
    if (X->ndim > 0) {
      for (int64_t i = 0; i < X->shape[0]; i++) {
        DLTensor _Y, _X;
        dltensor_strip_dim(&_Y, Y, i);
        dltensor_strip_dim(&_X, X, i);
        kernel_aic_layernorm_fp(&_Y, &_X, Scale, B, axis - 1, epsilon);
      }
    }
  } else {
    // total length of the normalized dimensions
    int64_t length = 1;
    for (int i = 0; i < X->ndim; i++) {
      length *= X->shape[i];
    }

    // length of that vector is the result of vsetvl with the shape of the tensor's last dimension
    uint32_t vl = __riscv_vsetvl_e32m2(X->shape[X->ndim - 1]);

    // sum all dimensions of tensor X onto a vector
    vfloat32m2_t vsum = rvv_tensor_sum_f32m2(__riscv_vfmv_v_f_f32m2(0.f, vl), X);

    // summation reduction of remaining elements in the vector and division by length to obtain mean
    vsum               = vfredusum_f32m2(vsum, vl);
    vfloat32m2_t vmean = __riscv_vfmul_vf_f32m2(vsum, 1.f / (float)length, 1);

    // broadcast mean to whole vector
    for (uint32_t log2_sz = 0; (2 << log2_sz) <= (int)CEIL_POW2(vl); log2_sz++) {
      vmean = __riscv_vslideup_vx_f32m2(vmean, vmean, 1 << log2_sz, 2 << log2_sz);
    }

    // sum the squared differences w.r.t. the mean of all dimensions of tensor X onto a vector
    vfloat32m2x2_t vsqsum_vmean = rvv_tensor_squared_diff_sum_f32m2(__riscv_vfmv_v_f_f32m2(-0.f, vl), X, vmean);
    vfloat32m2_t   vsqsum       = __riscv_vget_v_f32m2x2_f32m2(vsqsum_vmean, 0);
    vmean                       = __riscv_vget_v_f32m2x2_f32m2(vsqsum_vmean, 1);

    // summation reduction of remaining elements and division by length to obtain variance
    vsqsum            = vfredusum_f32m2(vsqsum, vl);
    vfloat32m2_t vvar = __riscv_vfmul_vf_f32m2(vsqsum, 1.f / (float)length, 1);

    // take inverse square-root of variance + epsilon to obtain inverse of standard deviation
    if (epsilon != (_Float16)0.) {
      vvar = __riscv_vfadd_vf_f32m2(vvar, (float)epsilon, 1);
    }
    vfloat32m2_t vstd_inv = __riscv_vfrsqrt7_v_f32m2(vvar, 1);

    // broadcast inverse of standard deviation to whole vector
    for (uint32_t log2_sz = 0; (2 << log2_sz) <= (int)CEIL_POW2(vl); log2_sz++) {
      vstd_inv = __riscv_vslideup_vx_f32m2(vstd_inv, vstd_inv, 1 << log2_sz, 2 << log2_sz);
    }

    // normalize tensor data
    rvv_tensor_normalize(Y, X, __riscv_vfneg_v_f32m2(vmean, vl), vstd_inv, Scale, B);
  }
}

vfloat32m2_t rvv_tensor_sum_f32m2(vfloat32m2_t vsum, const DLTensor *X) {
  if (X->ndim > 1) {
    for (int64_t i = 0; i < X->shape[0]; i++) {
      DLTensor _X;
      dltensor_strip_dim(&_X, X, i);
      vsum = rvv_tensor_sum_f32m2(vsum, &_X);
    }
  } else {
    uint32_t vl       = __riscv_vsetvl_e32m2(X->shape[0]);
    int64_t  bstride  = dltensor_bstride(X, 0);
    int64_t  data_inc = bstride * vl;
    void    *data     = X->data;
    for (int64_t i = 0; i < X->shape[0]; i += vl, data = ((uint8_t *)data) + data_inc) {
      vl                 = __riscv_vsetvl_e32m2(X->shape[0] - i);
      vfloat16m1_t vin16 = __riscv_vlse16_v_f16m1(data, bstride, vl);
      vsum               = __riscv_vfwadd_wv_f32m2(vsum, vin16, vl);
    }
  }
  return vsum;
}

vfloat32m2x2_t rvv_tensor_squared_diff_sum_f32m2(vfloat32m2_t vsum, const DLTensor *X, vfloat32m2_t vsub) {
  if (X->ndim > 1) {
    for (int64_t i = 0; i < X->shape[0]; i++) {
      DLTensor _X;
      dltensor_strip_dim(&_X, X, i);
      vfloat32m2x2_t vsum_vsub = rvv_tensor_squared_diff_sum_f32m2(vsum, &_X, vsub);
      vsum                     = __riscv_vget_v_f32m2x2_f32m2(vsum_vsub, 0);
      vsub                     = __riscv_vget_v_f32m2x2_f32m2(vsum_vsub, 1);
    }
  } else {
    uint32_t vl       = __riscv_vsetvl_e32m2(X->shape[0]);
    int64_t  bstride  = dltensor_bstride(X, 0);
    int64_t  data_inc = bstride * vl;
    void    *data     = X->data;
    for (int64_t i = 0; i < X->shape[0]; i += vl, data = ((uint8_t *)data) + data_inc) {
      vl                 = __riscv_vsetvl_e32m2(X->shape[0] - i);
      vfloat16m1_t vin16 = __riscv_vlse16_v_f16m1(data, bstride, vl);
      vfloat32m2_t vdiff = __riscv_vfwsub_wv_f32m2(vsub, vin16, vl);
      vfloat32m2_t vsq   = __riscv_vfmul_vv_f32m2(vdiff, vdiff, vl);
      vsum               = __riscv_vfadd_vv_f32m2(vsum, vsq, vl);
    }
  }
  vfloat32m2x2_t ret = __riscv_vundefined_f32m2x2();
  ret = __riscv_vset_v_f32m2_f32m2x2(ret, 0, vsum);
  ret = __riscv_vset_v_f32m2_f32m2x2(ret, 1, vsub);
  return ret;
}

vfloat32m2x2_t rvv_tensor_normalize(DLTensor *Y, const DLTensor *X, vfloat32m2_t vmean_neg, vfloat32m2_t vstd_inv,
                                    const DLTensor *Scale, const DLTensor *B) {
  if (X->ndim > 1) {
    for (int64_t i = 0; i < X->shape[0]; i++) {
      DLTensor _Y, _X, _Scale, _B;
      dltensor_strip_dim(&_Y, Y, i);
      dltensor_strip_dim(&_X, X, i);
      dltensor_strip_dim(&_Scale, Scale, i);
      dltensor_strip_dim(&_B, B, i);
      vfloat32m2x2_t vmean_neg_vstd_inv = rvv_tensor_normalize(&_Y, &_X, vmean_neg, vstd_inv, &_Scale, &_B);
      vmean_neg                         = __riscv_vget_v_f32m2x2_f32m2(vmean_neg_vstd_inv, 0);
      vstd_inv                          = __riscv_vget_v_f32m2x2_f32m2(vmean_neg_vstd_inv, 1);
    }
  } else {
    uint32_t vl         = __riscv_vsetvl_e32m2(X->shape[0]);
    int64_t  X_bstride  = dltensor_bstride(X, 0);
    int64_t  Y_bstride  = dltensor_bstride(Y, 0);
    int64_t  S_bstride  = dltensor_bstride(Scale, 0);
    int64_t  B_bstride  = dltensor_bstride(B, 0);
    int64_t  X_data_inc = X_bstride * vl;
    int64_t  Y_data_inc = Y_bstride * vl;
    int64_t  S_data_inc = S_bstride * vl;
    int64_t  B_data_inc = B_bstride * vl;
    void    *X_data     = X->data;
    void    *Y_data     = Y->data;
    void    *S_data     = Scale->data;
    void    *B_data     = B->data;
    for (int64_t i = 0; i < X->shape[0]; i += vl) {
      // load data and convert to fp32
      vl                 = __riscv_vsetvl_e32m2(X->shape[0] - i);
      vfloat16m1_t vin16 = __riscv_vlse16_v_f16m1(X_data, X_bstride, vl);

      // normalize by adding negated mean and multiplying with inverse of standard deviation
      vfloat32m2_t vdiff = __riscv_vfwadd_wv_f32m2(vmean_neg, vin16, vl);
      vfloat32m2_t vnorm = __riscv_vfmul_vv_f32m2(vdiff, vstd_inv, vl);

      // multiply by scale and add bias
      vfloat16m1_t vscale16 = __riscv_vlse16_v_f16m1(S_data, S_bstride, vl);
      vfloat16m1_t vbias16  = __riscv_vlse16_v_f16m1(B_data, B_bstride, vl);
      vfloat32m2_t vscale   = __riscv_vfwcvt_f_f_v_f32m2(vscale16, vl);
      vnorm                 = __riscv_vfwadd_wv_f32m2(__riscv_vfmul_vv_f32m2(vnorm, vscale, vl), vbias16, vl);

      // convert back to fp16 and store data
      vfloat16m1_t vout16 = __riscv_vfncvt_f_f_w_f16m1(vnorm, vl);
      __riscv_vsse16_v_f16m1(Y_data, Y_bstride, vout16, vl);

      X_data = ((uint8_t *)X_data) + X_data_inc;
      Y_data = ((uint8_t *)Y_data) + Y_data_inc;
      S_data = ((uint8_t *)S_data) + S_data_inc;
      B_data = ((uint8_t *)B_data) + B_data_inc;
    }
  }
  vfloat32m2x2_t ret = __riscv_vundefined_f32m2x2();
  ret = __riscv_vset_v_f32m2_f32m2x2(ret, 0, vmean_neg);
  ret = __riscv_vset_v_f32m2_f32m2x2(ret, 1, vstd_inv);
  return ret;
}
