// Description: dwconv2d kernel
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#include <dwconv2d.h>
#include <platform.h>
#include <testutils.h>
#include <printf.h>

void dwconv2d_fp32(int8_t *tensor, int32_t n, int32_t h, int32_t w, int32_t c, int8_t *filters, int32_t f,
                   int8_t *output, float *a, float *b) {
  int32_t cplane = h * w;
  int32_t nplane = c * cplane;

  int32_t o_idx = 0;

  for (int32_t ni = 0; ni < n; ni++) {
    for (int32_t ci = 0; ci < c; ci++) {
      int8_t *filter = filters + ci * f * f;
      int32_t i_idx_ = ni * nplane + ci * cplane;
      for (int32_t hi = 0; hi < h - f + 1; hi++) {
        for (int32_t wi = 0; wi < w - f + 1; wi++) {
          int32_t accum = 0;

          for (int32_t fy = 0; fy < f; fy++) {
            int32_t hi_ = hi + fy;

            for (int32_t fx = 0; fx < f; fx++) {
              int32_t wi_ = wi + fx;

              int32_t i_idx = i_idx_ + hi_ * w + wi_;
              int32_t f_idx = fy * f + fx;

              int16_t mult = (int16_t)tensor[i_idx] * (int16_t)filter[f_idx];
              accum        += (int32_t)mult;
            }
          }
          // Requantize
          float quant = (float)accum;
          quant       = a[ci] * quant + b[ci];

          if (quant > INT8_MAX) quant = INT8_MAX;
          if (quant < INT8_MIN) quant = INT8_MIN;

          // Round to nearest, tie to even
          uint32_t rne = 0xe0;
          asm volatile("csrrc x0, fcsr, %0" ::"r"(rne));
          int8_t rnd;
          asm volatile("fcvt.l.s %0, %1" : "=r"(rnd) : "f"(quant));
          output[o_idx++] = rnd;
        }
      }
    }
  }
}

void dwconv2d_fp16(int8_t *tensor, int32_t n, int32_t h, int32_t w, int32_t c, int8_t *filters, int32_t f,
                   int8_t *output, _Float16 *a, _Float16 *b, int32_t *q) {
  int32_t cplane = h * w;
  int32_t nplane = c * cplane;

  int32_t o_idx = 0;

  for (int32_t ni = 0; ni < n; ni++) {
    for (int32_t ci = 0; ci < c; ci++) {
      int8_t *filter = filters + ci * f * f;
      int32_t i_idx_ = ni * nplane + ci * cplane;
      for (int32_t hi = 0; hi < h - f + 1; hi++) {
        for (int32_t wi = 0; wi < w - f + 1; wi++) {
          int32_t accum = 0;

          for (int32_t fy = 0; fy < f; fy++) {
            int32_t hi_ = hi + fy;

            for (int32_t fx = 0; fx < f; fx++) {
              int32_t wi_ = wi + fx;

              int32_t i_idx = i_idx_ + hi_ * w + wi_;
              int32_t f_idx = fy * f + fx;

              int16_t mult = (int16_t)tensor[i_idx] * (int16_t)filter[f_idx];
              accum        += (int32_t)mult;
            }
          }
          // Requantize
          _Float16 quant = (_Float16)(accum >> q[ci]);
          quant          = a[ci] * quant;
          quant          += b[ci];

          if (quant > INT8_MAX) quant = INT8_MAX;
          if (quant < INT8_MIN) quant = INT8_MIN;

          int32_t rnd;
          asm volatile("fcvt.w.h %0, %1, rne" : "=r"(rnd) : "f"(quant));
          output[o_idx++] = (int8_t)rnd;
        }
      }
    }
  }
}

void dwconv2d_fp32_rvv(int8_t *tensor, int32_t n, int32_t h, int32_t w, int32_t c, int8_t *filters, int32_t f,
                       int8_t *output, float *a, float *b) {
  if (w < f || h < f) {
    printf(
        "Tensor of size %ix%i is too small. Needs to be larger than the "
        "filter of size %ix%i\n",
        w, h, f, f);
  }
  if (f == 7) {
    if ((h - f + 1) % 2 != 0) {
      printf("Unsupported input tensor size\n");
      exit(TEST_FAILURE);
    }
    for (int32_t ni = 0; ni < n; ni++) {
      dwconv2d_fp32_7xVL_rvv(tensor + ni * (c * h * w), h, w, c, filters, f,
                             output + ni * (c * (h - f + 1) * (w - f + 1)), a, b);
    }
  } else if (f == 3) {
    if ((h - f + 1) % 4 != 0) {
      printf("Unsupported input tensor size\n");
      exit(TEST_FAILURE);
    }
    for (int32_t ni = 0; ni < n; ni++) {
      dwconv2d_fp32_3xVL_rvv(tensor + ni * (c * h * w), h, w, c, filters, f,
                             output + ni * (c * (h - f + 1) * (w - f + 1)), a, b);
    }
  } else {
    printf("Unimplemented filter size of %i\n", f);
    exit(TEST_FAILURE);
  }
}

#define REQUANT_FP32(VS, A, B, LMULe32, LMULe16, LMULe8)      \
  {                                                           \
    uint32_t rne = 0xe0;                                      \
    asm volatile("csrrc x0, fcsr, %0" ::"r"(rne));            \
    asm volatile("vsetvli x0, x0, e32, " LMULe32 ", ta, ma"); \
    asm volatile("vfcvt.f.x.v " VS ", " VS "");               \
    asm volatile("vfmul.vf " VS ", " VS ", %0" ::"f"(A));     \
    asm volatile("vfadd.vf " VS ", " VS ", %0" ::"f"(B));     \
    float max = (float)INT8_MAX;                              \
    asm volatile("vfmin.vf " VS ", " VS ", %0" ::"f"(max));   \
    float min = (float)INT8_MIN;                              \
    asm volatile("vfmax.vf " VS ", " VS ", %0" ::"f"(min));   \
    asm volatile("vsetvli x0, x0, e16, " LMULe16 ", ta, ma"); \
    asm volatile("vfncvt.x.f.w " VS ", " VS "");              \
    asm volatile("vsetvli x0, x0, e8, " LMULe8 ", ta, ma");   \
    asm volatile("vncvt.x.x.w " VS ", " VS "");               \
  }

void dwconv2d_fp32_7xVL_rvv(int8_t *tensor, int32_t h, int32_t w, int32_t c, int8_t *filters, int32_t f, int8_t *output,
                            float *a, float *b) {
  // We work on 2 rows of the output matrix at once
  // We work on concurrent_rows + f - 1 rows of the input matrix at once
  int32_t concurrent_rows = 2;

  int32_t vl;
  int32_t lwi = w;
  int32_t lwf = f;
  int32_t lwo = w - f + 1;
  int32_t lho = h - f + 1;

  for (int32_t ci = 0; ci < c; ci++) {
    asm volatile("vsetvli %0, %1, e8, mf4, ta, ma" : "=r"(vl) : "r"(lwo));

    float a_param = a[ci];
    float b_param = b[ci];

    for (int32_t w_pos = 0; w_pos < lwo; w_pos += vl) {
      asm volatile("vsetvli %0, %1, e8, mf4, ta, ma" : "=r"(vl) : "r"(lwo - w_pos));

      int8_t *i      = tensor + w_pos;
      int8_t *o      = output + w_pos;
      int8_t *filter = filters;

      int16_t t0, t1, t2, t3, t4, t5, t6;
      t0 = (int16_t)*filter;
      t1 = (int16_t) * (filter + lwf);

      // Preload rows
      int8_t *i_row = i;
      asm volatile("vle8.v v7,  (%0)" ::"r"(i_row));
      asm volatile("vwcvt.x.x.v v4, v7");
      i_row += lwi;
      asm volatile("vle8.v v7,  (%0)" ::"r"(i_row));
      asm volatile("vwcvt.x.x.v v6, v7");
      i_row += lwi;
      asm volatile("vle8.v v7,  (%0)" ::"r"(i_row));
      asm volatile("vwcvt.x.x.v v8, v7");
      i_row += lwi;
      asm volatile("vle8.v v7,  (%0)" ::"r"(i_row));
      asm volatile("vwcvt.x.x.v v10, v7");
      i_row += lwi;
      asm volatile("vle8.v v7,  (%0)" ::"r"(i_row));
      asm volatile("vwcvt.x.x.v v12, v7");
      i_row += lwi;
      asm volatile("vle8.v v7,  (%0)" ::"r"(i_row));
      asm volatile("vwcvt.x.x.v v14, v7");

      asm volatile("vsetvli x0, x0, e16, mf2, ta, ma");
      asm volatile("vwmul.vx v5, v4, %0" ::"r"(t0));
      asm volatile("vwmul.vx v2, v6, %0" ::"r"(t0));

      // Iterate over the output rows
      for (int32_t row = 0; row < lho; row += concurrent_rows) {
        // Helper variables
        int8_t *weight = filter + lwf * 2;
        int8_t *o_     = o;
        int16_t sld_elem;

        asm volatile("vwmacc.vx v5, %0, v6" ::"r"(t1));

        int8_t *i_sld = i + vl;
        int8_t *i_row = i + (f - 1) * lwi;

        t2     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vwmacc.vx v2, %0, v8" ::"r"(t1));
        asm volatile("vmv.v.v v9, v8");

        asm volatile("vsetvli x0, x0, e8, mf4, ta, ma");
        asm volatile("vle8.v v7, (%0)" ::"r"(i_row));
        asm volatile("vwcvt.x.x.v v16, v7");
        asm volatile("vsetvli x0, x0, e16, mf2, ta, ma");
        i_row += lwi;

        t3     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vwmacc.vx v5, %0, v8" ::"r"(t2));
        asm volatile("vmv.v.v v11, v10");
        asm volatile("vwmacc.vx v2, %0, v10" ::"r"(t2));

        t4     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vwmacc.vx v5, %0, v10" ::"r"(t3));
        asm volatile("vmv.v.v v13, v12");
        asm volatile("vwmacc.vx v2, %0, v12" ::"r"(t3));

        asm volatile("vsetvli x0, x0, e8, mf4, ta, ma");
        asm volatile("vle8.v v7, (%0)" ::"r"(i_row));
        asm volatile("vwcvt.x.x.v v18, v7");
        asm volatile("vsetvli x0, x0, e16, mf2, ta, ma");

        t5     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vwmacc.vx v5, %0, v12" ::"r"(t4));
        asm volatile("vmv.v.v v15, v14");
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v2, %0, v14" ::"r"(t4));

        t6 = (int16_t)*weight;
        asm volatile("vwmacc.vx v5, %0, v14" ::"r"(t5));
        asm volatile("vmv.v.v v17, v16");
        asm volatile("vwmacc.vx v2, %0, v16" ::"r"(t5));

        asm volatile("vmv.v.v v19, v18");
        weight = filter + 1;
        t0     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vwmacc.vx v5, %0, v16" ::"r"(t6));
        asm volatile("vslide1down.vx v20, v4, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v2, %0, v18" ::"r"(t6));

        for (int32_t idx = 1; idx < f - 1; idx += 2) {
          // Fetch the other columns of the filter (except for the last one),
          // and start calculating their contributions on the two output rows
          // (v5, v2) To do so, at each iteration slide down the input rows by
          // one
          t1     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v5, %0, v20" ::"r"(t0));
          asm volatile("vslide1down.vx v22, v6, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;

          asm volatile("vwmacc.vx v2, %0, v22" ::"r"(t0));
          t2     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v5, %0, v22" ::"r"(t1));
          asm volatile("vslide1down.vx v24, v8, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;

          t3     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v5, %0, v24" ::"r"(t2));
          asm volatile("vslide1down.vx v26, v10, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v2, %0, v24" ::"r"(t1));

          t4     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v5, %0, v26" ::"r"(t3));
          asm volatile("vslide1down.vx v28, v12, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v2, %0, v26" ::"r"(t2));

          t5     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vslide1down.vx v30, v14, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v5, %0, v28" ::"r"(t4));
          asm volatile("vwmacc.vx v2, %0, v28" ::"r"(t3));

          t6 = (int16_t)*weight;
          asm volatile("vslide1down.vx v29, v16, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v5, %0, v30" ::"r"(t5));
          asm volatile("vwmacc.vx v2, %0, v30" ::"r"(t4));

          asm volatile("vslide1down.vx v31, v18, %0" ::"r"(sld_elem));
          i_sld    = i + vl + idx;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v5, %0, v29" ::"r"(t6));
          weight = filter + idx + 1;
          t0     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v2, %0, v29" ::"r"(t5));

          asm volatile("vslide1down.vx v4, v20, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v2, %0, v31" ::"r"(t6));

          if (idx + 2 >= f) continue;

          // Unroll 1

          t1     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v5, %0, v4" ::"r"(t0));
          asm volatile("vslide1down.vx v6, v22, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;

          asm volatile("vwmacc.vx v5, %0, v6" ::"r"(t1));
          t2     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v2, %0, v6" ::"r"(t0));
          asm volatile("vslide1down.vx v8, v24, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;

          t3     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v5, %0, v8" ::"r"(t2));
          asm volatile("vslide1down.vx v10, v26, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v2, %0, v8" ::"r"(t1));

          t4     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v5, %0, v10" ::"r"(t3));
          asm volatile("vslide1down.vx v12, v28, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v2, %0, v10" ::"r"(t2));

          t5     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v5, %0, v12" ::"r"(t4));
          asm volatile("vslide1down.vx v14, v30, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v2, %0, v12" ::"r"(t3));

          t6 = (int16_t)*weight;
          asm volatile("vwmacc.vx v5, %0, v14" ::"r"(t5));
          asm volatile("vslide1down.vx v16, v29, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v2, %0, v14" ::"r"(t4));

          asm volatile("vslide1down.vx v18, v31, %0" ::"r"(sld_elem));
          i_sld    = i + vl + idx + 1;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v5, %0, v16" ::"r"(t6));
          weight = filter + idx + 2;
          t0     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v2, %0, v16" ::"r"(t5));

          asm volatile("vslide1down.vx v20, v4, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v2, %0, v18" ::"r"(t6));
        }

        // Repeat for the last filter column, and then store the output rows
        asm volatile("vslide1down.vx v6, v22, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v5, %0, v4" ::"r"(t0));
        t1     = (int16_t)*weight;
        weight += lwf;

        asm volatile("vslide1down.vx v8, v24, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v5, %0, v6" ::"r"(t1));
        t2     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vmv.v.v v4, v9");
        asm volatile("vwmacc.vx v2, %0, v6" ::"r"(t0));

        asm volatile("vslide1down.vx v10, v26, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v5, %0, v8" ::"r"(t2));
        t3     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vmv.v.v v6, v11");
        asm volatile("vwmacc.vx v2, %0, v8" ::"r"(t1));

        t4     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vslide1down.vx v12, v28, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v5, %0, v10" ::"r"(t3));

        t5     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vslide1down.vx v14, v30, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v5, %0, v12" ::"r"(t4));
        asm volatile("vmv.v.v v8, v13");

        t6     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vwmacc.vx v5, %0, v14" ::"r"(t5));
        asm volatile("vslide1down.vx v16, v29, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;

        asm volatile("vwmacc.vx v5, %0, v16" ::"r"(t6));

        // Prefetch new filter weights
        t0 = (int16_t)*filter;
        t1 = (int16_t) * (filter + lwf);

        REQUANT_FP32("v5", a_param, b_param, "m1", "mf2", "mf4");
        asm volatile("vse8.v  v5, (%0)" ::"r"(o_));
        asm volatile("vsetvli x0, x0, e16, mf2, ta, ma");
        o_ += lwo;

        asm volatile("vwmacc.vx v2, %0, v10" ::"r"(t2));
        asm volatile("vmv.v.v v10, v15");
        asm volatile("vwmacc.vx v2, %0, v12" ::"r"(t3));
        asm volatile("vmv.v.v v12, v17");
        asm volatile("vwmacc.vx v2, %0, v14" ::"r"(t4));
        asm volatile("vslide1down.vx v18, v31, %0" ::"r"(sld_elem));

        asm volatile("vwmacc.vx v2, %0, v16" ::"r"(t5));
        asm volatile("vmv.v.v v14, v19");

        asm volatile("vwmacc.vx v2, %0, v18" ::"r"(t6));

        REQUANT_FP32("v2", a_param, b_param, "m1", "mf2", "mf4");
        asm volatile("vse8.v  v2, (%0)" ::"r"(o_));
        asm volatile("vsetvli x0, x0, e16, mf2, ta, ma");

        i += concurrent_rows * lwi;
        o += concurrent_rows * lwo;

        asm volatile("vwmul.vx v5, v4, %0" ::"r"(t0));
        asm volatile("vwmul.vx v2, v6, %0" ::"r"(t0));
      }
    }

    tensor  += h * w;
    output  += lho * lwo;
    filters += f * f;
  }
}

void dwconv2d_fp32_3xVL_rvv(int8_t *tensor, int32_t h, int32_t w, int32_t c, int8_t *filters, int32_t f, int8_t *output,
                            float *a, float *b) {
  // We work on 4 rows of the output matrix at once
  // We work on concurrent_rows + f - 1 rows of the input matrix at once
  int32_t concurrent_rows = 4;

  int32_t vl;
  int32_t lwi = w;
  int32_t lwf = f;
  int32_t lwo = w - f + 1;
  int32_t lho = h - f + 1;

  for (int32_t ci = 0; ci < c; ci++) {
    asm volatile("vsetvli %0, %1, e8, mf2, ta, ma" : "=r"(vl) : "r"(lwo));

    float a_param = a[ci];
    float b_param = b[ci];

    for (int32_t w_pos = 0; w_pos < lwo; w_pos += vl) {
      asm volatile("vsetvli %0, %1, e8, mf2, ta, ma" : "=r"(vl) : "r"(lwo - w_pos));

      int8_t *i      = tensor + w_pos;
      int8_t *o      = output + w_pos;
      int8_t *filter = filters;

      // Preload t0 and t1
      int16_t t0, t1, t2;
      t0 = (int16_t)*filter;
      t1 = (int16_t) * (filter + lwf);

      // Preload rows
      int8_t *i_row = i;
      asm volatile("vle8.v v0, (%0)" ::"r"(i_row));
      asm volatile("vwcvt.x.x.v v8, v0");
      i_row += lwi;
      asm volatile("vle8.v v0, (%0)" ::"r"(i_row));
      asm volatile("vwcvt.x.x.v v10, v0");

      asm volatile("vsetvli x0, x0, e16, m1, ta, ma");
      asm volatile("vwmul.vx v24, v8, %0" ::"r"(t0));
      asm volatile("vwmul.vx v2, v10, %0" ::"r"(t0));

      // Iterate over the output rows
      for (int32_t row = 0; row < lho; row += concurrent_rows) {
        // Helper variables
        int8_t *weight = filter + lwf * 2;
        int8_t *o_     = o;
        int16_t sld_elem;

        int8_t *i_sld = i + vl;
        int8_t *i_row = i + (f - 1) * lwi;

        asm volatile("vsetvli x0, x0, e8, mf2, ta, ma");
        asm volatile("vle8.v v0, (%0)" ::"r"(i_row));
        asm volatile("vwcvt.x.x.v v12, v0");
        asm volatile("vsetvli x0, x0, e16, m1, ta, ma");
        i_row    += lwi;
        sld_elem = (int16_t)*i_sld;

        asm volatile("vwmacc.vx v24, %0, v10" ::"r"(t1));
        asm volatile("vwmul.vx v4, v12, %0" ::"r"(t0));

        asm volatile("vsetvli x0, x0, e8, mf2, ta, ma");
        asm volatile("vle8.v v0, (%0)" ::"r"(i_row));
        asm volatile("vwcvt.x.x.v v14, v0");
        asm volatile("vsetvli x0, x0, e16, m1, ta, ma");
        i_row += lwi;

        t2 = (int16_t)*weight;
        asm volatile("vslide1down.vx v20, v8, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;

        asm volatile("vwmacc.vx v2, %0, v12" ::"r"(t1));
        asm volatile("vwmacc.vx v24, %0, v12" ::"r"(t2));

        asm volatile("vwmul.vx v6, v14, %0" ::"r"(t0));

        asm volatile("vsetvli x0, x0, e8, mf2, ta, ma");
        asm volatile("vle8.v v0, (%0)" ::"r"(i_row));
        asm volatile("vwcvt.x.x.v v16, v0");
        asm volatile("vsetvli x0, x0, e16, m1, ta, ma");
        i_row += lwi;

        asm volatile("vwmacc.vx v4, %0, v14" ::"r"(t1));
        asm volatile("vwmacc.vx v2, %0, v14" ::"r"(t2));
        asm volatile("vwmacc.vx v6, %0, v16" ::"r"(t1));

        asm volatile("vsetvli x0, x0, e8, mf2, ta, ma");
        asm volatile("vle8.v v0, (%0)" ::"r"(i_row));
        asm volatile("vwcvt.x.x.v v18, v0");
        asm volatile("vsetvli x0, x0, e16, m1, ta, ma");

        weight = filter + 1;
        t0     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vwmacc.vx v4, %0, v16" ::"r"(t2));

        // Fetch the middle column of the filter, and start calculating its
        // contributions on the output rows To do so, slide down the input rows
        // by one
        t1     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vslide1down.vx v22, v10, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v24, %0, v20" ::"r"(t0));
        asm volatile("vwmacc.vx v6, %0, v18" ::"r"(t2));

        t2 = (int16_t)*weight;
        asm volatile("vslide1down.vx v0, v12, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v24, %0, v22" ::"r"(t1));
        asm volatile("vwmacc.vx v2, %0, v22" ::"r"(t0));

        asm volatile("vslide1down.vx v26, v14, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v24, %0, v0" ::"r"(t2));
        asm volatile("vwmacc.vx v2, %0, v0" ::"r"(t1));
        asm volatile("vwmacc.vx v4, %0, v0" ::"r"(t0));

        asm volatile("vslide1down.vx v28, v16, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v2, %0, v26" ::"r"(t2));
        asm volatile("vwmacc.vx v4, %0, v26" ::"r"(t1));
        asm volatile("vwmacc.vx v6, %0, v26" ::"r"(t0));

        asm volatile("vslide1down.vx v30, v18, %0" ::"r"(sld_elem));
        i_sld    = i + vl + 1;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v4, %0, v28" ::"r"(t2));
        asm volatile("vwmacc.vx v6, %0, v28" ::"r"(t1));

        weight = filter + 2;
        t0     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vslide1down.vx v8, v20, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v6, %0, v30" ::"r"(t2));

        // Repeat for the last filter column, and then store the output rows
        t1     = (int16_t)*weight;
        weight += lwf;

        asm volatile("vslide1down.vx v10, v22, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;

        asm volatile("vwmacc.vx v24, %0, v8" ::"r"(t0));
        asm volatile("vmv.v.v v8, v16");
        t2 = (int16_t)*weight;

        asm volatile("vslide1down.vx v12, v0, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;

        asm volatile("vwmacc.vx v24, %0, v10" ::"r"(t1));
        asm volatile("vwmacc.vx v24, %0, v12" ::"r"(t2));

        i_sld                += lwi;
        int16_t sld_elem_tmp = (int16_t)*i_sld;

        REQUANT_FP32("v24", a_param, b_param, "m2", "m1", "mf2");
        asm volatile("vse8.v  v24, (%0)" ::"r"(o_));
        asm volatile("vsetvli x0, x0, e16, m1, ta, ma");
        o_ += lwo;

        asm volatile("vwmacc.vx v2, %0, v10" ::"r"(t0));
        asm volatile("vmv.v.v v10, v18");

        asm volatile("vwmacc.vx v2, %0, v12" ::"r"(t1));
        asm volatile("vwmacc.vx v4, %0, v12" ::"r"(t0));

        asm volatile("vslide1down.vx v14, v26, %0" ::"r"(sld_elem));
        asm volatile("vwmacc.vx v2, %0, v14" ::"r"(t2));
        asm volatile("vslide1down.vx v16, v28, %0" ::"r"(sld_elem_tmp));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;

        REQUANT_FP32("v2", a_param, b_param, "m2", "m1", "mf2");
        asm volatile("vse8.v  v2, (%0)" ::"r"(o_));
        asm volatile("vsetvli x0, x0, e16, m1, ta, ma");
        o_ += lwo;

        asm volatile("vwmacc.vx v4, %0, v14" ::"r"(t1));
        asm volatile("vwmacc.vx v6, %0, v14" ::"r"(t0));

        asm volatile("vwmacc.vx v4, %0, v16" ::"r"(t2));
        weight = filter;
        t0     = (int16_t)*weight;
        weight += lwf;

        REQUANT_FP32("v4", a_param, b_param, "m2", "m1", "mf2");
        asm volatile("vse8.v  v4, (%0)" ::"r"(o_));
        asm volatile("vsetvli x0, x0, e16, m1, ta, ma");
        o_ += lwo;

        asm volatile("vwmacc.vx v6, %0, v16" ::"r"(t1));
        asm volatile("vslide1down.vx v18, v30, %0" ::"r"(sld_elem));

        asm volatile("vwmacc.vx v6, %0, v18" ::"r"(t2));
        t1 = (int16_t)*weight;

        REQUANT_FP32("v6", a_param, b_param, "m2", "m1", "mf2");
        asm volatile("vse8.v  v6, (%0)" ::"r"(o_));
        asm volatile("vsetvli x0, x0, e16, m1, ta, ma");

        i += concurrent_rows * lwi;
        o += concurrent_rows * lwo;

        asm volatile("vwmul.vx v24, v8, %0" ::"r"(t0));
        asm volatile("vwmul.vx v2, v10, %0" ::"r"(t0));
      }
    }

    tensor  += h * w;
    output  += lho * lwo;
    filters += f * f;
  }
}

void dwconv2d_fp16_rvv(int8_t *tensor, int32_t n, int32_t h, int32_t w, int32_t c, int8_t *filters, int32_t f,
                       int8_t *output, _Float16 *a, _Float16 *b, int32_t *q) {
  if (w < f || h < f) {
    printf(
        "Tensor of size %ix%i is too small. Needs to be larger than the "
        "filter of size %ix%i\n",
        w, h, f, f);
  }
  if (f == 7) {
    if ((h - f + 1) % 2 != 0) {
      printf("Unsupported input tensor size\n");
      exit(TEST_FAILURE);
    }
    for (int32_t ni = 0; ni < n; ni++) {
      dwconv2d_fp16_7xVL_rvv(tensor + ni * (c * h * w), h, w, c, filters, f,
                             output + ni * (c * (h - f + 1) * (w - f + 1)), a, b, q);
    }
  } else if (f == 3) {
    if ((h - f + 1) % 4 != 0) {
      printf("Unsupported input tensor size\n");
      exit(TEST_FAILURE);
    }
    for (int32_t ni = 0; ni < n; ni++) {
      dwconv2d_fp16_3xVL_rvv(tensor + ni * (c * h * w), h, w, c, filters, f,
                             output + ni * (c * (h - f + 1) * (w - f + 1)), a, b, q);
    }
  } else {
    printf("Unimplemented filter size of %i\n", f);
    exit(TEST_FAILURE);
  }
}

#define REQUANT_FP16(VS, A, B, Q, LMULe8)                   \
  {                                                         \
    uint32_t rne = 0xe0;                                    \
    asm volatile("csrrc x0, fcsr, %0" ::"r"(rne));          \
    asm volatile("vnsra.wx " VS ", " VS ", %0" ::"r"(Q));   \
    asm volatile("vfcvt.f.x.v " VS ", " VS "");             \
    asm volatile("vfmul.vf " VS ", " VS ", %0" ::"f"(A));   \
    asm volatile("vfadd.vf " VS ", " VS ", %0" ::"f"(B));   \
    _Float16 max = (_Float16)INT8_MAX;                      \
    asm volatile("vfmin.vf " VS ", " VS ", %0" ::"f"(max)); \
    _Float16 min = (_Float16)INT8_MIN;                      \
    asm volatile("vfmax.vf " VS ", " VS ", %0" ::"f"(min)); \
    asm volatile("vsetvli x0, x0, e8, " LMULe8 ", ta, ma"); \
    asm volatile("vfncvt.x.f.w " VS ", " VS "");            \
  }

void dwconv2d_fp16_7xVL_rvv(int8_t *tensor, int32_t h, int32_t w, int32_t c, int8_t *filters, int32_t f, int8_t *output,
                            _Float16 *a, _Float16 *b, int32_t *q) {
  // We work on 2 rows of the output matrix at once
  // We work on concurrent_rows + f - 1 rows of the input matrix at once
  int32_t concurrent_rows = 2;

  int32_t vl;
  int32_t lwi = w;
  int32_t lwf = f;
  int32_t lwo = w - f + 1;
  int32_t lho = h - f + 1;

  for (int32_t ci = 0; ci < c; ci++) {
    asm volatile("vsetvli %0, %1, e8, mf4, ta, ma" : "=r"(vl) : "r"(lwo));

    _Float16 a_param = a[ci];
    _Float16 b_param = b[ci];
    int32_t  q_param = q[ci];

    for (int32_t w_pos = 0; w_pos < lwo; w_pos += vl) {
      asm volatile("vsetvli %0, %1, e8, mf4, ta, ma" : "=r"(vl) : "r"(lwo - w_pos));

      int8_t *i      = tensor + w_pos;
      int8_t *o      = output + w_pos;
      int8_t *filter = filters;

      int16_t t0, t1, t2, t3, t4, t5, t6;
      t0 = (int16_t)*filter;
      t1 = (int16_t) * (filter + lwf);

      // Preload rows
      int8_t *i_row = i;
      asm volatile("vle8.v v7,  (%0)" ::"r"(i_row));
      asm volatile("vwcvt.x.x.v v4, v7");
      i_row += lwi;
      asm volatile("vle8.v v7,  (%0)" ::"r"(i_row));
      asm volatile("vwcvt.x.x.v v6, v7");
      i_row += lwi;
      asm volatile("vle8.v v7,  (%0)" ::"r"(i_row));
      asm volatile("vwcvt.x.x.v v8, v7");
      i_row += lwi;
      asm volatile("vle8.v v7,  (%0)" ::"r"(i_row));
      asm volatile("vwcvt.x.x.v v10, v7");
      i_row += lwi;
      asm volatile("vle8.v v7,  (%0)" ::"r"(i_row));
      asm volatile("vwcvt.x.x.v v12, v7");
      i_row += lwi;
      asm volatile("vle8.v v7,  (%0)" ::"r"(i_row));
      asm volatile("vwcvt.x.x.v v14, v7");

      asm volatile("vsetvli x0, x0, e16, mf2, ta, ma");
      asm volatile("vwmul.vx v5, v4, %0" ::"r"(t0));
      asm volatile("vwmul.vx v2, v6, %0" ::"r"(t0));

      // Iterate over the output rows
      for (int32_t row = 0; row < lho; row += concurrent_rows) {
        // Helper variables
        int8_t *weight = filter + lwf * 2;
        int8_t *o_     = o;
        int16_t sld_elem;

        asm volatile("vwmacc.vx v5, %0, v6" ::"r"(t1));

        int8_t *i_sld = i + vl;
        int8_t *i_row = i + (f - 1) * lwi;

        t2     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vwmacc.vx v2, %0, v8" ::"r"(t1));
        asm volatile("vmv.v.v v9, v8");

        asm volatile("vsetvli x0, x0, e8, mf4, ta, ma");
        asm volatile("vle8.v v7, (%0)" ::"r"(i_row));
        asm volatile("vwcvt.x.x.v v16, v7");
        asm volatile("vsetvli x0, x0, e16, mf2, ta, ma");
        i_row += lwi;

        t3     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vwmacc.vx v5, %0, v8" ::"r"(t2));
        asm volatile("vmv.v.v v11, v10");
        asm volatile("vwmacc.vx v2, %0, v10" ::"r"(t2));

        t4     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vwmacc.vx v5, %0, v10" ::"r"(t3));
        asm volatile("vmv.v.v v13, v12");
        asm volatile("vwmacc.vx v2, %0, v12" ::"r"(t3));

        asm volatile("vsetvli x0, x0, e8, mf4, ta, ma");
        asm volatile("vle8.v v7, (%0)" ::"r"(i_row));
        asm volatile("vwcvt.x.x.v v18, v7");
        asm volatile("vsetvli x0, x0, e16, mf2, ta, ma");

        t5     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vwmacc.vx v5, %0, v12" ::"r"(t4));
        asm volatile("vmv.v.v v15, v14");
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v2, %0, v14" ::"r"(t4));

        t6 = (int16_t)*weight;
        asm volatile("vwmacc.vx v5, %0, v14" ::"r"(t5));
        asm volatile("vmv.v.v v17, v16");
        asm volatile("vwmacc.vx v2, %0, v16" ::"r"(t5));

        asm volatile("vmv.v.v v19, v18");
        weight = filter + 1;
        t0     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vwmacc.vx v5, %0, v16" ::"r"(t6));
        asm volatile("vslide1down.vx v20, v4, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v2, %0, v18" ::"r"(t6));

        for (int32_t idx = 1; idx < f - 1; idx += 2) {
          // Fetch the other columns of the filter (except for the last one),
          // and start calculating their contributions on the two output rows
          // (v5, v2) To do so, at each iteration slide down the input rows by
          // one
          t1     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v5, %0, v20" ::"r"(t0));
          asm volatile("vslide1down.vx v22, v6, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;

          asm volatile("vwmacc.vx v2, %0, v22" ::"r"(t0));
          t2     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v5, %0, v22" ::"r"(t1));
          asm volatile("vslide1down.vx v24, v8, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;

          t3     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v5, %0, v24" ::"r"(t2));
          asm volatile("vslide1down.vx v26, v10, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v2, %0, v24" ::"r"(t1));

          t4     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v5, %0, v26" ::"r"(t3));
          asm volatile("vslide1down.vx v28, v12, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v2, %0, v26" ::"r"(t2));

          t5     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vslide1down.vx v30, v14, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v5, %0, v28" ::"r"(t4));
          asm volatile("vwmacc.vx v2, %0, v28" ::"r"(t3));

          t6 = (int16_t)*weight;
          asm volatile("vslide1down.vx v29, v16, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v5, %0, v30" ::"r"(t5));
          asm volatile("vwmacc.vx v2, %0, v30" ::"r"(t4));

          asm volatile("vslide1down.vx v31, v18, %0" ::"r"(sld_elem));
          i_sld    = i + vl + idx;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v5, %0, v29" ::"r"(t6));
          weight = filter + idx + 1;
          t0     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v2, %0, v29" ::"r"(t5));

          asm volatile("vslide1down.vx v4, v20, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v2, %0, v31" ::"r"(t6));

          if (idx + 2 >= f) continue;

          // Unroll 1

          t1     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v5, %0, v4" ::"r"(t0));
          asm volatile("vslide1down.vx v6, v22, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;

          asm volatile("vwmacc.vx v5, %0, v6" ::"r"(t1));
          t2     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v2, %0, v6" ::"r"(t0));
          asm volatile("vslide1down.vx v8, v24, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;

          t3     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v5, %0, v8" ::"r"(t2));
          asm volatile("vslide1down.vx v10, v26, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v2, %0, v8" ::"r"(t1));

          t4     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v5, %0, v10" ::"r"(t3));
          asm volatile("vslide1down.vx v12, v28, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v2, %0, v10" ::"r"(t2));

          t5     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v5, %0, v12" ::"r"(t4));
          asm volatile("vslide1down.vx v14, v30, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v2, %0, v12" ::"r"(t3));

          t6 = (int16_t)*weight;
          asm volatile("vwmacc.vx v5, %0, v14" ::"r"(t5));
          asm volatile("vslide1down.vx v16, v29, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v2, %0, v14" ::"r"(t4));

          asm volatile("vslide1down.vx v18, v31, %0" ::"r"(sld_elem));
          i_sld    = i + vl + idx + 1;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v5, %0, v16" ::"r"(t6));
          weight = filter + idx + 2;
          t0     = (int16_t)*weight;
          weight += lwf;
          asm volatile("vwmacc.vx v2, %0, v16" ::"r"(t5));

          asm volatile("vslide1down.vx v20, v4, %0" ::"r"(sld_elem));
          i_sld    += lwi;
          sld_elem = (int16_t)*i_sld;
          asm volatile("vwmacc.vx v2, %0, v18" ::"r"(t6));
        }

        // Repeat for the last filter column, and then store the output rows
        asm volatile("vslide1down.vx v6, v22, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v5, %0, v4" ::"r"(t0));
        t1     = (int16_t)*weight;
        weight += lwf;

        asm volatile("vslide1down.vx v8, v24, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v5, %0, v6" ::"r"(t1));
        t2     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vmv.v.v v4, v9");
        asm volatile("vwmacc.vx v2, %0, v6" ::"r"(t0));

        asm volatile("vslide1down.vx v10, v26, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v5, %0, v8" ::"r"(t2));
        t3     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vmv.v.v v6, v11");
        asm volatile("vwmacc.vx v2, %0, v8" ::"r"(t1));

        t4     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vslide1down.vx v12, v28, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v5, %0, v10" ::"r"(t3));

        t5     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vslide1down.vx v14, v30, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v5, %0, v12" ::"r"(t4));
        asm volatile("vmv.v.v v8, v13");

        t6     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vwmacc.vx v5, %0, v14" ::"r"(t5));
        asm volatile("vslide1down.vx v16, v29, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;

        asm volatile("vwmacc.vx v5, %0, v16" ::"r"(t6));

        // Prefetch new filter weights
        t0 = (int16_t)*filter;
        t1 = (int16_t) * (filter + lwf);

        REQUANT_FP16("v5", a_param, b_param, q_param, "mf4");
        asm volatile("vse8.v  v5, (%0)" ::"r"(o_));
        asm volatile("vsetvli x0, x0, e16, mf2, ta, ma");
        o_ += lwo;

        asm volatile("vwmacc.vx v2, %0, v10" ::"r"(t2));
        asm volatile("vmv.v.v v10, v15");
        asm volatile("vwmacc.vx v2, %0, v12" ::"r"(t3));
        asm volatile("vmv.v.v v12, v17");
        asm volatile("vwmacc.vx v2, %0, v14" ::"r"(t4));
        asm volatile("vslide1down.vx v18, v31, %0" ::"r"(sld_elem));

        asm volatile("vwmacc.vx v2, %0, v16" ::"r"(t5));
        asm volatile("vmv.v.v v14, v19");

        asm volatile("vwmacc.vx v2, %0, v18" ::"r"(t6));

        REQUANT_FP16("v2", a_param, b_param, q_param, "mf4");
        asm volatile("vse8.v  v2, (%0)" ::"r"(o_));
        asm volatile("vsetvli x0, x0, e16, mf2, ta, ma");

        i += concurrent_rows * lwi;
        o += concurrent_rows * lwo;

        asm volatile("vwmul.vx v5, v4, %0" ::"r"(t0));
        asm volatile("vwmul.vx v2, v6, %0" ::"r"(t0));
      }
    }

    tensor  += h * w;
    output  += lho * lwo;
    filters += f * f;
  }
}

void dwconv2d_fp16_3xVL_rvv(int8_t *tensor, int32_t h, int32_t w, int32_t c, int8_t *filters, int32_t f, int8_t *output,
                            _Float16 *a, _Float16 *b, int32_t *q) {
  // We work on 4 rows of the output matrix at once
  // We work on concurrent_rows + f - 1 rows of the input matrix at once
  int32_t concurrent_rows = 4;
  int32_t vl;
  int32_t lwi = w;
  int32_t lwf = f;
  int32_t lwo = w - f + 1;
  int32_t lho = h - f + 1;

  for (int32_t ci = 0; ci < c; ci++) {
    asm volatile("vsetvli %0, %1, e8, mf2, ta, ma" : "=r"(vl) : "r"(lwo));

    _Float16 a_param = a[ci];
    _Float16 b_param = b[ci];
    int32_t  q_param = q[ci];

    for (int32_t w_pos = 0; w_pos < lwo; w_pos += vl) {
      asm volatile("vsetvli %0, %1, e8, mf2, ta, ma" : "=r"(vl) : "r"(lwo - w_pos));

      int8_t *i      = tensor + w_pos;
      int8_t *o      = output + w_pos;
      int8_t *filter = filters;

      // Preload t0 and t1
      int16_t t0, t1, t2;
      t0 = (int16_t)*filter;
      t1 = (int16_t) * (filter + lwf);

      // Preload rows
      int8_t *i_row = i;
      asm volatile("vle8.v v0, (%0)" ::"r"(i_row));
      asm volatile("vwcvt.x.x.v v8, v0");
      i_row += lwi;
      asm volatile("vle8.v v0, (%0)" ::"r"(i_row));
      asm volatile("vwcvt.x.x.v v10, v0");

      asm volatile("vsetvli x0, x0, e16, m1, ta, ma");
      asm volatile("vwmul.vx v24, v8, %0" ::"r"(t0));
      asm volatile("vwmul.vx v2, v10, %0" ::"r"(t0));

      // Iterate over the output rows
      for (int32_t row = 0; row < lho; row += concurrent_rows) {
        // Helper variables
        int8_t *weight = filter + lwf * 2;
        int8_t *o_     = o;
        int16_t sld_elem;

        int8_t *i_sld = i + vl;
        int8_t *i_row = i + (f - 1) * lwi;

        asm volatile("vsetvli x0, x0, e8, mf2, ta, ma");
        asm volatile("vle8.v v0, (%0)" ::"r"(i_row));
        asm volatile("vwcvt.x.x.v v12, v0");
        asm volatile("vsetvli x0, x0, e16, m1, ta, ma");
        i_row    += lwi;
        sld_elem = (int16_t)*i_sld;

        asm volatile("vwmacc.vx v24, %0, v10" ::"r"(t1));
        asm volatile("vwmul.vx v4, v12, %0" ::"r"(t0));

        asm volatile("vsetvli x0, x0, e8, mf2, ta, ma");
        asm volatile("vle8.v v0, (%0)" ::"r"(i_row));
        asm volatile("vwcvt.x.x.v v14, v0");
        asm volatile("vsetvli x0, x0, e16, m1, ta, ma");
        i_row += lwi;

        t2 = (int16_t)*weight;
        asm volatile("vslide1down.vx v20, v8, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;

        asm volatile("vwmacc.vx v2, %0, v12" ::"r"(t1));
        asm volatile("vwmacc.vx v24, %0, v12" ::"r"(t2));

        asm volatile("vwmul.vx v6, v14, %0" ::"r"(t0));

        asm volatile("vsetvli x0, x0, e8, mf2, ta, ma");
        asm volatile("vle8.v v0, (%0)" ::"r"(i_row));
        asm volatile("vwcvt.x.x.v v16, v0");
        asm volatile("vsetvli x0, x0, e16, m1, ta, ma");
        i_row += lwi;

        asm volatile("vwmacc.vx v4, %0, v14" ::"r"(t1));
        asm volatile("vwmacc.vx v2, %0, v14" ::"r"(t2));
        asm volatile("vwmacc.vx v6, %0, v16" ::"r"(t1));

        asm volatile("vsetvli x0, x0, e8, mf2, ta, ma");
        asm volatile("vle8.v v0, (%0)" ::"r"(i_row));
        asm volatile("vwcvt.x.x.v v18, v0");
        asm volatile("vsetvli x0, x0, e16, m1, ta, ma");

        weight = filter + 1;
        t0     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vwmacc.vx v4, %0, v16" ::"r"(t2));

        // Fetch the middle column of the filter, and start calculating its
        // contributions on the output rows To do so, slide down the input rows
        // by one
        t1     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vslide1down.vx v22, v10, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v24, %0, v20" ::"r"(t0));
        asm volatile("vwmacc.vx v6, %0, v18" ::"r"(t2));

        t2 = (int16_t)*weight;
        asm volatile("vslide1down.vx v0, v12, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v24, %0, v22" ::"r"(t1));
        asm volatile("vwmacc.vx v2, %0, v22" ::"r"(t0));

        asm volatile("vslide1down.vx v26, v14, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v24, %0, v0" ::"r"(t2));
        asm volatile("vwmacc.vx v2, %0, v0" ::"r"(t1));
        asm volatile("vwmacc.vx v4, %0, v0" ::"r"(t0));

        asm volatile("vslide1down.vx v28, v16, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v2, %0, v26" ::"r"(t2));
        asm volatile("vwmacc.vx v4, %0, v26" ::"r"(t1));
        asm volatile("vwmacc.vx v6, %0, v26" ::"r"(t0));

        asm volatile("vslide1down.vx v30, v18, %0" ::"r"(sld_elem));
        i_sld    = i + vl + 1;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v4, %0, v28" ::"r"(t2));
        asm volatile("vwmacc.vx v6, %0, v28" ::"r"(t1));

        weight = filter + 2;
        t0     = (int16_t)*weight;
        weight += lwf;
        asm volatile("vslide1down.vx v8, v20, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;
        asm volatile("vwmacc.vx v6, %0, v30" ::"r"(t2));

        // Repeat for the last filter column, and then store the output rows
        t1     = (int16_t)*weight;
        weight += lwf;

        asm volatile("vslide1down.vx v10, v22, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;

        asm volatile("vwmacc.vx v24, %0, v8" ::"r"(t0));
        asm volatile("vmv.v.v v8, v16");
        t2 = (int16_t)*weight;

        asm volatile("vslide1down.vx v12, v0, %0" ::"r"(sld_elem));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;

        asm volatile("vwmacc.vx v24, %0, v10" ::"r"(t1));
        asm volatile("vwmacc.vx v24, %0, v12" ::"r"(t2));

        i_sld                += lwi;
        int16_t sld_elem_tmp = (int16_t)*i_sld;

        REQUANT_FP16("v24", a_param, b_param, q_param, "mf2");
        asm volatile("vse8.v  v24, (%0)" ::"r"(o_));
        asm volatile("vsetvli x0, x0, e16, m1, ta, ma");
        o_ += lwo;

        asm volatile("vwmacc.vx v2, %0, v10" ::"r"(t0));
        asm volatile("vmv.v.v v10, v18");

        asm volatile("vwmacc.vx v2, %0, v12" ::"r"(t1));
        asm volatile("vwmacc.vx v4, %0, v12" ::"r"(t0));

        asm volatile("vslide1down.vx v14, v26, %0" ::"r"(sld_elem));
        asm volatile("vwmacc.vx v2, %0, v14" ::"r"(t2));
        asm volatile("vslide1down.vx v16, v28, %0" ::"r"(sld_elem_tmp));
        i_sld    += lwi;
        sld_elem = (int16_t)*i_sld;

        REQUANT_FP16("v2", a_param, b_param, q_param, "mf2");
        asm volatile("vse8.v  v2, (%0)" ::"r"(o_));
        asm volatile("vsetvli x0, x0, e16, m1, ta, ma");
        o_ += lwo;

        asm volatile("vwmacc.vx v4, %0, v14" ::"r"(t1));
        asm volatile("vwmacc.vx v6, %0, v14" ::"r"(t0));

        asm volatile("vwmacc.vx v4, %0, v16" ::"r"(t2));
        weight = filter;
        t0     = (int16_t)*weight;
        weight += lwf;

        REQUANT_FP16("v4", a_param, b_param, q_param, "mf2");
        asm volatile("vse8.v  v4, (%0)" ::"r"(o_));
        asm volatile("vsetvli x0, x0, e16, m1, ta, ma");
        o_ += lwo;

        asm volatile("vwmacc.vx v6, %0, v16" ::"r"(t1));
        asm volatile("vslide1down.vx v18, v30, %0" ::"r"(sld_elem));

        asm volatile("vwmacc.vx v6, %0, v18" ::"r"(t2));
        t1 = (int16_t)*weight;

        REQUANT_FP16("v6", a_param, b_param, q_param, "mf2");
        asm volatile("vse8.v  v6, (%0)" ::"r"(o_));
        asm volatile("vsetvli x0, x0, e16, m1, ta, ma");

        i += concurrent_rows * lwi;
        o += concurrent_rows * lwo;

        asm volatile("vwmul.vx v24, v8, %0" ::"r"(t0));
        asm volatile("vwmul.vx v2, v10, %0" ::"r"(t0));
      }
    }

    tensor  += h * w;
    output  += lho * lwo;
    filters += f * f;
  }
}
