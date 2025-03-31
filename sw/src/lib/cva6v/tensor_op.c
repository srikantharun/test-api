// Description: Tensor operations
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#include <tensor_op.h>
#include <math.h>
#include <printf.h>

#define INT_ABS(x) (((x) < 0) ? (uint64_t)(-(x)) : (uint64_t)(x))

#define FLOAT32_EXP_MASK 0x7F800000ul
#define FLOAT16_EXP_MASK 0x7C00u

void print_tensor_float32(float *matrix, uint32_t n, uint32_t w, uint32_t h, uint32_t c, uint32_t format) {
  for (uint32_t i = 0; i < n; i++) {
    if (format == TENSOR_FORMAT_NHWC) {
      for (uint32_t y = 0; y < h; y++) {
        for (uint32_t x = 0; x < w; x++) {
          printf("( ");
          for (uint32_t e = 0; e < c; e++) {
            printf("%f ", *(double*)matrix++);
          }
          printf(") ");
        }
        printf("\n");
      }
    } else if (format == TENSOR_FORMAT_NCHW) {
      for (uint32_t e = 0; e < c; e++) {
        printf("Channel %i\n", e);
        for (uint32_t y = 0; y < h; y++) {
          for (uint32_t x = 0; x < w; x++) {
            printf("%f ", *(double*)matrix++);
          }
          printf("\n");
        }
      }
    }
    if (n - 1 > i) printf("\n");
  }
}

void print_tensor_float16(_Float16 *matrix, uint32_t n, uint32_t w, uint32_t h, uint32_t c, uint32_t format) {
  for (uint32_t i = 0; i < n; i++) {
    if (format == TENSOR_FORMAT_NHWC) {
      for (uint32_t y = 0; y < h; y++) {
        for (uint32_t x = 0; x < w; x++) {
          printf("( ");
          for (uint32_t e = 0; e < c; e++) {
            printf("%f ", *(double*)matrix++);
          }
          printf(") ");
        }
        printf("\n");
      }
    } else if (format == TENSOR_FORMAT_NCHW) {
      for (uint32_t e = 0; e < c; e++) {
        printf("Channel %i\n", e);
        for (uint32_t y = 0; y < h; y++) {
          for (uint32_t x = 0; x < w; x++) {
            printf("%f ", *(double*)matrix++);
          }
          printf("\n");
        }
      }
    }
    if (n - (uint32_t)1 > i) printf("\n");
  }
}

void print_tensor_uint8(uint8_t *matrix, uint32_t n, uint32_t w, uint32_t h, uint32_t c, uint32_t format) {
  for (uint32_t i = 0; i < n; i++) {
    if (format == TENSOR_FORMAT_NHWC) {
      for (uint32_t y = 0; y < h; y++) {
        for (uint32_t x = 0; x < w; x++) {
          printf("( ");
          for (uint32_t e = 0; e < c; e++) {
            printf("%u ", *matrix++);
          }
          printf(") ");
        }
        printf("\n");
      }
    } else if (format == TENSOR_FORMAT_NCHW) {
      for (uint32_t e = 0; e < c; e++) {
        printf("Channel %i\n", e);
        for (uint32_t y = 0; y < h; y++) {
          for (uint32_t x = 0; x < w; x++) {
            printf("%u ", *matrix++);
          }
          printf("\n");
        }
      }
    }
    if (n - 1 > i) printf("\n");
  }
}

void print_tensor_int8(int8_t *matrix, uint32_t n, uint32_t w, uint32_t h, uint32_t c, uint32_t format) {
  for (uint32_t i = 0; i < n; i++) {
    if (format == TENSOR_FORMAT_NHWC) {
      for (uint32_t y = 0; y < h; y++) {
        for (uint32_t x = 0; x < w; x++) {
          printf("( ");
          for (uint32_t e = 0; e < c; e++) {
            printf("%i ", *matrix++);
          }
          printf(") ");
        }
        printf("\n");
      }
    } else if (format == TENSOR_FORMAT_NCHW) {
      for (uint32_t e = 0; e < c; e++) {
        printf("Channel %i\n", e);
        for (uint32_t y = 0; y < h; y++) {
          for (uint32_t x = 0; x < w; x++) {
            printf("%i ", *matrix++);
          }
          printf("\n");
        }
      }
    }
    if (n - 1 > i) printf("\n");
  }
}

void print_tensor_int32(int32_t *matrix, uint32_t n, uint32_t w, uint32_t h, uint32_t c, uint32_t format) {
  for (uint32_t i = 0; i < n; i++) {
    if (format == TENSOR_FORMAT_NHWC) {
      for (uint32_t y = 0; y < h; y++) {
        for (uint32_t x = 0; x < w; x++) {
          printf("( ");
          for (uint32_t e = 0; e < c; e++) {
            printf("%i ", *matrix++);
          }
          printf(") ");
        }
        printf("\n");
      }
    } else if (format == TENSOR_FORMAT_NCHW) {
      for (uint32_t e = 0; e < c; e++) {
        printf("Channel %i\n", e);
        for (uint32_t y = 0; y < h; y++) {
          for (uint32_t x = 0; x < w; x++) {
            printf("%i ", *matrix++);
          }
          printf("\n");
        }
      }
    }
    if (n - 1 > i) printf("\n");
  }
}

void init_tensor_float16(_Float16 *matrix, uint32_t n, uint32_t h, uint32_t w, uint32_t c, _Float16 s_a, _Float16 s_b,
                         _Float16 s_c, _Float16 s_d, _Float16 s_e, uint32_t format) {
  uint32_t c_offset;
  uint32_t w_offset;
  uint32_t h_offset;
  uint32_t n_offset;
  if (format == TENSOR_FORMAT_NHWC) {
    c_offset = 1;
    w_offset = c;
    h_offset = w * w_offset;
    n_offset = h * h_offset;
  } else {
    w_offset = 1;
    h_offset = w;
    c_offset = h * h_offset;
    n_offset = c * c_offset;
  }
  for (uint32_t i = 0; i < n; i++) {
    for (uint32_t y = 0; y < h; y++) {
      for (uint32_t x = 0; x < w; x++) {
        for (uint32_t e = 0; e < c; e++) {
          _Float16 val = s_a * i + s_b * y + s_c * x + s_d * e + s_e;
          matrix[i * n_offset + y * h_offset + x * w_offset + e * c_offset] = val;
        }
      }
    }
  }
}

void init_tensor_uint8(uint8_t *matrix, uint32_t n, uint32_t h, uint32_t w, uint32_t c, uint8_t s_a, uint8_t s_b,
                       uint8_t s_c, uint8_t s_d, uint8_t s_e, uint32_t format) {
  uint32_t c_offset;
  uint32_t w_offset;
  uint32_t h_offset;
  uint32_t n_offset;
  if (format == TENSOR_FORMAT_NHWC) {
    c_offset = 1;
    w_offset = c;
    h_offset = w * w_offset;
    n_offset = h * h_offset;
  } else {
    w_offset = 1;
    h_offset = w;
    c_offset = h * h_offset;
    n_offset = c * c_offset;
  }
  for (uint32_t i = 0; i < n; i++) {
    for (uint32_t y = 0; y < h; y++) {
      for (uint32_t x = 0; x < w; x++) {
        for (uint32_t e = 0; e < c; e++) {
          uint8_t val = s_a * i + s_b * y + s_c * x + s_d * e + s_e;
          matrix[i * n_offset + y * h_offset + x * w_offset + e * c_offset] = val;
        }
      }
    }
  }
}

void init_tensor_int8(int8_t *matrix, int32_t n, uint32_t h, uint32_t w, uint32_t c, int8_t s_a, int8_t s_b, int8_t s_c,
                      int8_t s_d, int8_t s_e, uint32_t format) {
  uint32_t c_offset;
  uint32_t w_offset;
  uint32_t h_offset;
  uint32_t n_offset;
  if (format == TENSOR_FORMAT_NHWC) {
    c_offset = 1;
    w_offset = c;
    h_offset = w * w_offset;
    n_offset = h * h_offset;
  } else {
    w_offset = 1;
    h_offset = w;
    c_offset = h * h_offset;
    n_offset = c * c_offset;
  }
  for (int32_t i = 0; i < n; i++) {
    for (uint32_t y = 0; y < h; y++) {
      for (uint32_t x = 0; x < w; x++) {
        for (uint32_t e = 0; e < c; e++) {
          int8_t val = s_a * i + s_b * y + s_c * x + s_d * e + s_e;
          matrix[i * n_offset + y * h_offset + x * w_offset + e * c_offset] = val;
        }
      }
    }
  }
}

int compare_tensors_float_with_error_percentage(float *golden, float *tensor, uint32_t n, uint32_t h, uint32_t w,
                                                uint32_t c, float error) {
  for (uint32_t i = 0; i < n * h * w * c; i++) {
    float diff = fabsf(golden[i] - tensor[i]);
    if (fabsf(fabsf(golden[i] / tensor[i]) - 1.f) > error && ((*((uint32_t *)(&diff)) & FLOAT32_EXP_MASK))) {
      if (VERBOSE) {
        printf("i=%d: Expected value: %f, actual value: %f\n", i, (double)golden[i], (double)tensor[i]);
      }
      return i != 0 ? i : -1;
    }
  }
  return 0;
}

int compare_tensors_float_with_error(float *golden, float *tensor, uint32_t n, uint32_t h, uint32_t w, uint32_t c,
                                     float error) {
  for (uint32_t i = 0; i < n * h * w * c; i++) {
    if (fabsf(golden[i] - tensor[i]) > error) {
      if (VERBOSE) {
        printf("i=%d: Expected value: %f, actual value: %f\n", i, (double)golden[i], (double)tensor[i]);
      }
      return i != 0 ? i : -1;
    }
  }
  return 0;
}

int compare_tensors_float(float *golden, float *tensor, uint32_t n, uint32_t h, uint32_t w, uint32_t c) {
  return compare_tensors_float_with_error(golden, tensor, n, h, w, c, FLOAT_ERROR);
}

int compare_tensors_float16_with_error_percentage(_Float16 *golden, _Float16 *tensor, uint32_t n, uint32_t h,
                                                  uint32_t w, uint32_t c, _Float16 error) {
  for (uint32_t i = 0; i < n * h * w * c; i++) {
    _Float16 diff = (_Float16)fabsf((float)*golden - (float)*tensor);
    if (fabsf(fabsf((float)*golden / (float)*tensor) - 1.f) > (float)error && ((*((uint16_t *)(&diff)) & FLOAT16_EXP_MASK))) {
      if (VERBOSE) {
        printf("Expected value: %f, actual value: %f\n", (double)*golden, (double)*tensor);
        printf("%i\n", i);
      }
      return i != 0 ? i : -1;
    }
    golden++;
    tensor++;
  }
  return 0;
}

int compare_tensors_float16_with_error(_Float16 *golden, _Float16 *tensor, uint32_t n, uint32_t h, uint32_t w,
                                       uint32_t c, _Float16 error) {
  for (uint32_t i = 0; i < n * h * w * c; i++) {
    if (fabsf((float)*golden++ - (float)*tensor++) > (float)error) {
      if (VERBOSE) {
        printf("Expected value: %f, actual value: %f\n", (double)*--golden, (double)*--tensor);
        printf("%i\n", i);
      }
      return i != 0 ? i : -1;
    }
  }
  return 0;
}

int compare_tensors_float16(_Float16 *golden, _Float16 *tensor, uint32_t n, uint32_t h, uint32_t w, uint32_t c) {
  return compare_tensors_float16_with_error(golden, tensor, n, h, w, c, FLOAT16_ERROR);
}

int compare_tensors_uint8_with_error(uint8_t *golden, uint8_t *tensor, uint32_t n, uint32_t h, uint32_t w, uint32_t c,
                                     uint8_t error) {
  for (uint32_t i = 0; i < n * h * w * c; i++) {
    int16_t diff = (int16_t)(*tensor++) - (int16_t)(*golden++);
    if (INT_ABS(diff) > error) {
      if (VERBOSE) {
        printf("Expected value: %u, actual value: %u\n", *--golden, *--tensor);
      }
      return i != 0 ? i : -1;
    }
  }
  return 0;
}

int compare_tensors_uint8(uint8_t *golden, uint8_t *tensor, uint32_t n, uint32_t h, uint32_t w, uint32_t c) {
  return compare_tensors_uint8_with_error(golden, tensor, n, h, w, c, 0);
}

int compare_tensors_uint32_with_error(uint32_t *golden, uint32_t *tensor, uint32_t n, uint32_t h, uint32_t w,
                                      uint32_t c, uint32_t error) {
  for (uint32_t i = 0; i < n * h * w * c; i++) {
    int64_t diff = (int64_t)(*tensor++) - (int64_t)(*golden++);
    if (INT_ABS(diff) > error) {
      if (VERBOSE) {
        printf("Expected value: %u, actual value: %u\n", *--golden, *--tensor);
      }
      return i != 0 ? i : -1;
    }
  }
  return 0;
}

int compare_tensors_uint32(uint32_t *golden, uint32_t *tensor, uint32_t n, uint32_t h, uint32_t w, uint32_t c) {
  return compare_tensors_uint32_with_error(golden, tensor, n, h, w, c, 0);
}

int compare_tensors_int8_with_error(int8_t *golden, int8_t *tensor, uint32_t n, uint32_t h, uint32_t w, uint32_t c,
                                    uint8_t error) {
  for (uint32_t i = 0; i < n * h * w * c; i++) {
    int16_t diff = (int64_t)(*tensor++) - (int64_t)(*golden++);
    if (INT_ABS(diff) > error) {
      if (VERBOSE) {
        printf("Expected value: %i, actual value: %i\n", *--golden, *--tensor);
      }
      return i != 0 ? i : -1;
    }
  }
  return 0;
}

int compare_tensors_int8(int8_t *golden, int8_t *tensor, uint32_t n, uint32_t h, uint32_t w, uint32_t c) {
  return compare_tensors_int8_with_error(golden, tensor, n, h, w, c, 0);
}

int compare_tensors_int32_with_error(int32_t *golden, int32_t *tensor, uint32_t n, uint32_t h, uint32_t w, uint32_t c,
                                     uint32_t error) {
  for (uint32_t i = 0; i < n * h * w * c; i++) {
    int64_t diff = (int64_t)(*tensor++) - (int64_t)(*golden++);
    if (INT_ABS(diff) > error) {
      if (VERBOSE) {
        printf("Expected value: %u, actual value: %u\n", *--golden, *--tensor);
      }
      return i != 0 ? i : -1;
    }
  }
  return 0;
}

int compare_tensors_int32(int32_t *golden, int32_t *tensor, uint32_t n, uint32_t h, uint32_t w, uint32_t c) {
  return compare_tensors_int32_with_error(golden, tensor, n, h, w, c, 0);
}

static int compare_dltensors_head(DLTensor *golden, DLTensor *tensor) {
  if (golden->dtype.code != tensor->dtype.code || golden->dtype.bits != tensor->dtype.bits ||
      golden->dtype.lanes != tensor->dtype.lanes) {
    printf("DLTensor dtype mismatch\n");
    return -1;
  }
  for (int i = 0; i < golden->ndim; i++) {
    if (golden->ndim != tensor->ndim || golden->shape[i] != tensor->shape[i]) {
      printf("DLTensor shape mismatch\n");
      return -1;
    }
  }
  return 0;
}

int compare_dltensors(DLTensor *golden, DLTensor *tensor) {
  return compare_dltensors_with_error(golden, tensor, FLOAT_ERROR);
}

int compare_dltensors_with_error(DLTensor *golden, DLTensor *tensor, float error) {
  if (compare_dltensors_head(golden, tensor) != 0) {
    return -1;
  }
  if (golden->ndim > 4 || golden->strides != NULL) {
    printf("DLTensor has more than 4 dimensions or unsupported strides - cannot compare\n");
    return -1;
  }
  uint32_t shape[4] = {1, 1, 1, 1};
  for (int i = 0; i < golden->ndim; i++) {
    shape[4 - golden->ndim + i] = golden->shape[i];
  }
  if (golden->dtype.code == kDLInt && golden->dtype.bits == 8 && golden->dtype.lanes == 1) {
    return compare_tensors_int8_with_error(golden->data, tensor->data, shape[0], shape[1], shape[2], shape[3], error);
  }
  if (golden->dtype.code == kDLInt && golden->dtype.bits == 32 && golden->dtype.lanes == 1) {
    return compare_tensors_int32_with_error(golden->data, tensor->data, shape[0], shape[1], shape[2], shape[3], error);
  }
  if (golden->dtype.code == kDLUInt && golden->dtype.bits == 8 && golden->dtype.lanes == 1) {
    return compare_tensors_uint8_with_error(golden->data, tensor->data, shape[0], shape[1], shape[2], shape[3], error);
  }
  if (golden->dtype.code == kDLUInt && golden->dtype.bits == 32 && golden->dtype.lanes == 1) {
    return compare_tensors_uint32_with_error(golden->data, tensor->data, shape[0], shape[1], shape[2], shape[3], error);
  }
  if (golden->dtype.code == kDLFloat && golden->dtype.bits == 16 && golden->dtype.lanes == 1) {
    return compare_tensors_float16_with_error(golden->data, tensor->data, shape[0], shape[1], shape[2], shape[3],
                                              error);
  }
  if (golden->dtype.code == kDLFloat && golden->dtype.bits == 32 && golden->dtype.lanes == 1) {
    return compare_tensors_float_with_error(golden->data, tensor->data, shape[0], shape[1], shape[2], shape[3], error);
  }
  printf("DLTensor has unsupported datatype (code %d, bits %d, lanes %d) - cannot compare\n", golden->dtype.code,
         golden->dtype.bits, golden->dtype.lanes);
  return -1;
}

int compare_dltensors_with_error_percentage(DLTensor *golden, DLTensor *tensor, float error) {
  if (compare_dltensors_head(golden, tensor) != 0) {
    return -1;
  }
  if (golden->ndim > 4 || golden->strides != NULL) {
    printf("DLTensor has more than 4 dimensions or unsupported strides - cannot compare\n");
    return -1;
  }
  uint32_t shape[4] = {1, 1, 1, 1};
  for (int i = 0; i < golden->ndim; i++) {
    shape[4 - golden->ndim + i] = golden->shape[i];
  }
  if (golden->dtype.code == kDLFloat && golden->dtype.bits == 16 && golden->dtype.lanes == 1) {
    return compare_tensors_float16_with_error_percentage(golden->data, tensor->data, shape[0], shape[1], shape[2],
                                                         shape[3], error);
  }
  if (golden->dtype.code == kDLFloat && golden->dtype.bits == 32 && golden->dtype.lanes == 1) {
    return compare_tensors_float_with_error_percentage(golden->data, tensor->data, shape[0], shape[1], shape[2],
                                                       shape[3], error);
  }
  printf("DLTensor has unsupported datatype (code %d, bits %d, lanes %d) - cannot compare\n", golden->dtype.code,
         golden->dtype.bits, golden->dtype.lanes);
  return -1;
}

void copy_tensor_float16(_Float16 *src, _Float16 *dst, uint32_t n, uint32_t h, uint32_t w, uint32_t c) {
  uint32_t size = n * h * w * c;
  for (uint32_t i = 0; i < size; i++) {
    *dst++ = *src++;
  }
}

void copy_tensor_int8(int8_t *src, int8_t *dst, uint32_t n, uint32_t h, uint32_t w, uint32_t c) {
  uint32_t size = n * h * w * c;
  for (uint32_t i = 0; i < size; i++) {
    *dst++ = *src++;
  }
}

void copy_tensor_uint8(uint8_t *src, uint8_t *dst, uint32_t n, uint32_t h, uint32_t w, uint32_t c) {
  uint32_t size = n * h * w * c;
  for (uint32_t i = 0; i < size; i++) {
    *dst++ = *src++;
  }
}
