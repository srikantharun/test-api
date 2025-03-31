// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DLPack utility functions
// Owner: Manuel Eggimann <manuel.eggimann@axelera.ai>
#include <dlpack_util.h>

#include <math.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#include <dlpack.h>
#include <log.h>
#include <printf.h>
#include <testutils.h>
#include <util.h>
#include <float.h>


#ifdef DLTENSOR_USE_VMEMCPY
#include <rvv_ops.h>
#define _memcpy vmemcpy
#else
#define _memcpy memcpy
#endif

typedef void (*printf_func_t)(char* fmt, ...);

#define PRINTF_CAST ((printf_func_t)_printf)

// Function definitions for printing various data types
static void print_int8(printf_func_t printf_func, void* x) {
    (*printf_func)("%3d", *((int8_t*)x));
}

static void print_int16(printf_func_t printf_func, void* x) {
    (*printf_func)("%5d", *((int16_t*)x));
}

static void print_int32(printf_func_t printf_func, void* x) {
    (*printf_func)("%9d", *((int32_t*)x));
}

static void print_int64(printf_func_t printf_func, void* x) {
    (*printf_func)("%10ld", *((int64_t*)x));
}

static void print_uint8(printf_func_t printf_func, void* x) {
    (*printf_func)("%3u", *((uint8_t*)x));
}

static void print_uint16(printf_func_t printf_func, void* x) {
    (*printf_func)("%5u", *((uint16_t*)x));
}

static void print_uint32(printf_func_t printf_func, void* x) {
    (*printf_func)("%10u", *((uint32_t*)x));
}

static void print_uint64(printf_func_t printf_func, void* x) {
    (*printf_func)("%10lu", *((uint64_t*)x));
}

static void print_float(printf_func_t printf_func, void* x) {
    (*printf_func)("%.4f", *(double*)((float*)x)); // cast to double, avoiding implicit conversion (variadic argument is promoted to double)
}

static void print_complex(printf_func_t printf_func, void* x) {
    double* complex_number = (double*)x; // cast to double, avoiding implicit conversion (variadic argument is promoted to double)
    double real_part = complex_number[0];
    double imag_part = complex_number[1];
    (*printf_func)("(%.4f + %.4f*i)", real_part, imag_part);
}

static void print_undef(printf_func_t printf_func, void* x) {
    UNUSED(x);
    (*printf_func)("XXX");
}

typedef void (*print_val_func_t)(printf_func_t printf_func, void* val);

print_val_func_t test = &print_int64;

// Given a dlpack dtype, the following function returns a function pointer,
// pointing to the right print implementation defined above.
static print_val_func_t get_print_func(DLDataType type) {
  switch (type.code) {
    case kDLBool:
    case kDLInt:
      if (type.bits > 32)
        return &print_int64;
      else if (type.bits > 16)
        return &print_int32;
      else if (type.bits > 8)
        return &print_int16;
      else
        return &print_int8;
      break;
    case kDLUInt:
      if (type.bits > 32)
        return &print_uint64;
      else if (type.bits > 16)
        return &print_uint32;
      else if (type.bits > 8)
        return &print_uint16;
      else
        return &print_uint8;
      break;
    case kDLBfloat:
      return &print_undef;
      break;
    case kDLFloat:
        return &print_float;
      break;
    case kDLComplex:
      return &print_complex;
      break;
    default:
      return &print_undef;
      break;
  }
}

// In this function, we further deal with vector typed values, again internally
// leveraging the appropriate print function to emmit the values.
static inline void print_val(DLDataType type, printf_func_t printf_func, print_val_func_t print, void* val) {
  if (type.lanes > 1) (*printf_func)("vector(");
  for (int i = 0; i < type.lanes; i++) {
    (*print)(printf_func, val);
    if (type.lanes > 1 && i != type.lanes - 1) (*printf_func)(",");
  }
  if (type.lanes > 1) (*printf_func)(")");
}

// Recursive function that internally determines the right print function to use
// and then recurses into each dimension for printing.
static inline void dltensor_print_internal(printf_func_t printf_func, const DLTensor* tensor, int linebreak_dim) {
  (*printf_func)("{");
  DLTensor         sub_tensor;
  print_val_func_t print            = get_print_func(tensor->dtype);
  void*            data_ptr         = tensor->data + tensor->byte_offset;
  size_t           outermost_stride = dltensor_bstride(tensor, 0);
  for (int i = 0; i < tensor->shape[0]; i++) {
    if (tensor->ndim > 1) {
      dltensor_strip_dim(&sub_tensor, tensor, i);
      dltensor_print_internal(printf_func, &sub_tensor, linebreak_dim);
    } else {
      // int64_t idx = 0;
      print_val(tensor->dtype, printf_func, print, data_ptr);
      data_ptr += outermost_stride;
    }
    if (i != tensor->shape[0] - 1) {
      (*printf_func)(", ");
      if (tensor->ndim > linebreak_dim) (*printf_func)("\n");
    }
  }
  (*printf_func)("}");
}

static void dltensor_info_wrap(const DLTensor* tensor, int level, printf_func_t printf_func) {
  if (config_log_level < level) {
        return;
  }
  (*printf_func)("{\n");
  char* type_code;
  switch (tensor->dtype.code) {
    case kDLInt:
      type_code = "int";
      break;
    case kDLUInt:
      type_code = "uint";
      break;
    case kDLFloat:
      type_code = "float";
      break;
    case kDLOpaqueHandle:
      type_code = "opaque_handle";
      break;
    case kDLBfloat:
      type_code = "BFloat";
      break;
    case kDLComplex:
      type_code = "Complex";
      break;
    case kDLBool:
      type_code = "bool";
      break;
    default:
      type_code = "unknown";
      break;
  }

  (*printf_func)("  dtype: { code: %s, bits: %d, lanes: %d}\n", type_code, tensor->dtype.bits, tensor->dtype.lanes);
  (*printf_func)("  shape: (");
  for (int i = 0; i < tensor->ndim; i++) {
    (*printf_func)("%ld", tensor->shape[i]);
    if (i != tensor->ndim - 1) (*printf_func)(", ");
  }
  (*printf_func)(")\n");
  if (tensor->strides == NULL) {
    (*printf_func)("  strides: packed, row-major\n");
  } else {
    (*printf_func)("  strides: (");
    for (int i = 0; i < tensor->ndim; i++) {
      (*printf_func)("%ld", tensor->strides[i]);
      if (i != tensor->ndim - 1) (*printf_func)(", ");
    }
    (*printf_func)(")\n");
  }
  (*printf_func)("  data_ptr: %p\n", tensor->data);
}

static void dltensor_print_wrap(const DLTensor* tensor, int linebreak_dim, int level, printf_func_t printf_func) {
  if (config_log_level < level) {
        return;
  }
  dltensor_info_wrap(tensor, level, printf_func);
  (*printf_func)("  data:\n");
  dltensor_print_internal(printf_func, tensor, linebreak_dim);
  (*printf_func)("\n}\n");
}

void dltensor_print(const DLTensor* tensor, int linebreak_dim) {
  dltensor_print_wrap(tensor, linebreak_dim, config_log_level, PRINTF_CAST); // not blocked by log level
}

void dltensor_logprint(int log_level, const DLTensor* tensor, int linebreak_dim) {
    if (is_valid_log_level(log_level)){
      dltensor_print_wrap(tensor, linebreak_dim, log_level, PRINTF_CAST);
    }
    else{
      LOG_ERR("Illegal log level");
    }
}

void dltensor_info(const DLTensor* tensor) {
  dltensor_info_wrap(tensor, config_log_level, PRINTF_CAST);
  printf("\n}\n");
}

void dltensor_loginfo(int log_level, const DLTensor* tensor) {
  if (is_valid_log_level(log_level)){
      dltensor_info_wrap(tensor, log_level, PRINTF_CAST);
      if (config_log_level >= log_level){
        printf("}\n");
      }
    }
    else{
      LOG_ERR("Illegal log level");
    }
}

// Cast functions from each supported type to float
static float uint8_t_to_float(void* x) {
    return (float)(*((uint8_t*)x));
}

static float uint16_t_to_float(void* x) {
    return (float)(*((uint16_t*)x));
}

static float uint32_t_to_float(void* x) {
    return (float)(*((uint32_t*)x));
}

static float uint64_t_to_float(void* x) {
    return (float)(*((uint64_t*)x));
}

static float int8_t_to_float(void* x) {
    return (float)(*((int8_t*)x));
}

static float int16_t_to_float(void* x) {
    return (float)(*((int16_t*)x));
}

static float int32_t_to_float(void* x) {
    return (float)(*((int32_t*)x));
}

static float int64_t_to_float(void* x) {
    return (float)(*((int64_t*)x));
}

static float float_to_float(void* x) {
    return (*((float*)x));
}

static float bool_to_float(void* x) {
    return (float)(*((bool*)x));
}

typedef float (*cast_func)(void*);

static inline cast_func get_cast_func(DLDataType t) {
  switch (t.code) {
    case kDLUInt:
      if (t.bits == 64)
        return &uint64_t_to_float;
      else if (t.bits == 32)
        return &uint32_t_to_float;
      else if (t.bits == 16)
        return &uint16_t_to_float;
      else if (t.bits == 8)
        return &uint8_t_to_float;
      break;
    case kDLInt:
      if (t.bits == 64)
        return &int64_t_to_float;
      else if (t.bits == 32)
        return &int32_t_to_float;
      else if (t.bits == 16)
        return &int16_t_to_float;
      else if (t.bits == 8)
        return &int8_t_to_float;
      break;
    case kDLBool:
      return &bool_to_float;
    case kDLFloat:
        return &float_to_float;
      break;
    default:
      break;
  }
  LOG_ERR("Unsupported DLPack datatype!");
  ASSERT(0); // exit
}

// Store functions from float type to each supported dtype
static void store_float_to_uint8_t(void* x, float val) {
    *((uint8_t*)x) = (uint8_t)val;
}

static void store_float_to_uint16_t(void* x, float val) {
    *((uint16_t*)x) = (uint16_t)val;
}

static void store_float_to_uint32_t(void* x, float val) {
    *((uint32_t*)x) = (uint32_t)val;
}

static void store_float_to_uint64_t(void* x, float val) {
    *((uint64_t*)x) = (uint64_t)val;
}

static void store_float_to_int8_t(void* x, float val) {
    *((int8_t*)x) = (int8_t)val;
}

static void store_float_to_int16_t(void* x, float val) {
    *((int16_t*)x) = (int16_t)val;
}

static void store_float_to_int32_t(void* x, float val) {
    *((int32_t*)x) = (int32_t)val;
}

static void store_float_to_int64_t(void* x, float val) {
    *((int64_t*)x) = (int64_t)val;
}

static void store_float_to_float(void* x, float val) {
    *((float*)x) = (float)val;
}

static void store_float_to_bool(void* x, float val) {
    *((bool*)x) = (bool)val;
}

typedef void (*store_val_func)(void*, float);

static inline store_val_func get_store_val_func(DLDataType t) {
  switch (t.code) {
    case kDLUInt:
      if (t.bits == 64)
        return &store_float_to_uint64_t;
      else if (t.bits == 32)
        return &store_float_to_uint32_t;
      else if (t.bits == 16)
        return &store_float_to_uint16_t;
      else if (t.bits == 8)
        return &store_float_to_uint8_t;
      break;
    case kDLInt:
      if (t.bits == 64)
        return &store_float_to_int64_t;
      else if (t.bits == 32)
        return &store_float_to_int32_t;
      else if (t.bits == 16)
        return &store_float_to_int16_t;
      else if (t.bits == 8)
        return &store_float_to_int8_t;
      break;
    case kDLBool:
      return &store_float_to_bool;
    case kDLFloat:
        return &store_float_to_float;
      break;
    default:
      break;
  }
  LOG_ERR("Unsupported DLPack datatype!");
  ASSERT(0); // exit
}

static float _dltensor_max(const DLTensor* t, float current_max) {
  float    max  = current_max;
  cast_func cast = get_cast_func(t->dtype);
  if (t->ndim > 1) {
    for (int i = 0; i < t->shape[0]; i++) {
      DLTensor sub_t;
      dltensor_strip_dim(&sub_t, t, i);
      float val = _dltensor_max(&sub_t, current_max);
      max        = (val > max) ? val : max;
    }
  } else {
    for (int i = 0; i < t->shape[0]; i++) {
      float val = (*cast)(dltensor_index(t, i));
      max        = (val > max) ? val : max;
    }
  }
  return max;
}

float dltensor_max(const DLTensor* t) {
  ASSERT(t->dtype.code != kDLComplex);
  ASSERT(t->dtype.code != kDLBfloat);
  ASSERT(t->data != NULL);
  ASSERT(t->dtype.lanes == 1);
  return _dltensor_max(t, -FLT_MAX);
}

static float _dltensor_sum(const DLTensor* t, float current_sum) {
  float    sum  = current_sum;
  cast_func cast = get_cast_func(t->dtype);
  if (t->ndim > 1) {
    for (int i = 0; i < t->shape[0]; i++) {
      DLTensor sub_t;
      dltensor_strip_dim(&sub_t, t, i);
      float val = _dltensor_sum(&sub_t, current_sum);
      sum        += val;
    }
  } else {
    for (int i = 0; i < t->shape[0]; i++) {
      float val = (*cast)(dltensor_index(t, i));
      sum        += val;
    }
  }
  return sum;
}

float dltensor_sum(const DLTensor* t) {
  ASSERT(t->dtype.code != kDLComplex);
  ASSERT(t->dtype.code != kDLBfloat);
  ASSERT(t->data != NULL);
  ASSERT(t->dtype.lanes == 1);
  return _dltensor_sum(t, 0.0);
}

static float _dltensor_sqerror_sum(const DLTensor* a, const DLTensor* b) {
  float sqerror_sum = 0;
  if (a->ndim > 1) {
    for (int i = 0; i < a->shape[0]; i++) {
      DLTensor sub_a, sub_b;
      dltensor_strip_dim(&sub_a, a, i);
      dltensor_strip_dim(&sub_b, b, i);
      sqerror_sum += _dltensor_sqerror_sum(&sub_a, &sub_b);
    }
  } else {
    cast_func cast = get_cast_func(a->dtype);
    for (int i = 0; i < a->shape[0]; i++) {
      float val_a = (*cast)(dltensor_index(a, i));
      float val_b = (*cast)(dltensor_index(b, i));
      float error = val_a - val_b;
      sqerror_sum  += error * error;
    }
  }
  return sqerror_sum;
}

float dltensor_mse(const DLTensor* a, const DLTensor* b) {
  ASSERT(a->ndim == b->ndim);
  for (int i = 0; i < a->ndim; i++) {
    ASSERT(a->shape[i] == b->shape[i]);
  }
  ASSERT(a->data != NULL);
  ASSERT(b->data != NULL);
  ASSERT(a->dtype.code == b->dtype.code);
  ASSERT(a->dtype.bits == b->dtype.bits);
  ASSERT(a->dtype.lanes == b->dtype.lanes);
  ASSERT(a->dtype.code != kDLComplex);
  ASSERT(a->dtype.code != kDLBfloat);
  ASSERT(a->dtype.lanes == 1);
  float   sqerror_sum  = _dltensor_sqerror_sum(a, b);
  uint64_t num_elements = dltensor_data_size(a) / dltensor_elem_size(a);
  return sqerror_sum / num_elements;
}

float dltensor_psnr(const DLTensor* ref, const DLTensor* noisy) {
  float max = dltensor_max(ref);
  float mse = dltensor_mse(ref, noisy);
  if (mse == 0) {
    return FLT_MAX;
  } else {
    return 10 * log10f(max * max / mse);
  }
}

int dltensor_get_num_packed_dims(const DLTensor* t) {
  if (t->strides == NULL) return t->ndim;
  int64_t packed_stride = 1;
  for (int i = t->ndim - 1; i >= 0; i--) {
    if (packed_stride != t->strides[i]) return t->ndim - i - 1;
    packed_stride *= t->shape[i];
  }
  return t->ndim;
}

bool dltensor_is_packed(const DLTensor* t) { return dltensor_get_num_packed_dims(t) == t->ndim; }

static void _dltensor_sub(DLTensor* dst, const DLTensor* a, const DLTensor* b) {
  if (a->ndim > 1) {
    for (int i = 0; i < a->shape[0]; i++) {
      DLTensor sub_dst, sub_a, sub_b;
      dltensor_strip_dim(&sub_a, a, i);
      dltensor_strip_dim(&sub_b, b, i);
      dltensor_strip_dim(&sub_dst, dst, i);
      _dltensor_sub(&sub_dst, &sub_a, &sub_b);
    }
  } else {
    cast_func      cast_src   = get_cast_func(a->dtype);
    store_val_func store_func = get_store_val_func(dst->dtype);
    for (int i = 0; i < a->shape[0]; i++) {
      float val_a = (*cast_src)(dltensor_index(a, i));
      float val_b = (*cast_src)(dltensor_index(b, i));
      float diff  = val_a - val_b;
      (*store_func)(dltensor_index(dst, i), diff);
    }
  }
}

void dltensor_sub(DLTensor* dst, const DLTensor* a, const DLTensor* b) {
  ASSERT(a->ndim == b->ndim);
  ASSERT(a->ndim == dst->ndim);
  for (int i = 0; i < a->ndim; i++) {
    ASSERT(a->shape[i] == b->shape[i]);
    ASSERT(a->shape[i] == dst->shape[i]);
  }
  ASSERT(a->data != NULL);
  ASSERT(b->data != NULL);
  ASSERT(dst->data != NULL);
  ASSERT(a->dtype.code == b->dtype.code);
  if (a->dtype.code == kDLUInt) ASSERT(dst->dtype.code == kDLUInt || dst->dtype.code == kDLInt);
  ASSERT(a->dtype.bits == b->dtype.bits);
  ASSERT(a->dtype.bits == dst->dtype.bits);
  ASSERT(a->dtype.lanes == b->dtype.lanes);
  ASSERT(a->dtype.lanes == dst->dtype.lanes);
  ASSERT(a->dtype.code != kDLComplex);
  ASSERT(a->dtype.code != kDLBfloat);
  ASSERT(a->dtype.lanes == 1);

  _dltensor_sub(dst, a, b);
}

static void _dltensor_abs(DLTensor* dst, const DLTensor* src) {
  if (src->ndim > 1) {
    for (int i = 0; i < src->shape[0]; i++) {
      DLTensor sub_dst, sub_src;
      dltensor_strip_dim(&sub_src, src, i);
      dltensor_strip_dim(&sub_dst, dst, i);
      _dltensor_abs(&sub_dst, &sub_src);
    }
  } else {
    cast_func      cast_src   = get_cast_func(src->dtype);
    store_val_func store_func = get_store_val_func(dst->dtype);
    for (int i = 0; i < src->shape[0]; i++) {
      float val_src = (*cast_src)(dltensor_index(src, i));
      (*store_func)(dltensor_index(dst, i), fabsf(val_src));
    }
  }
}

void dltensor_abs(DLTensor* dst, const DLTensor* src) {
  ASSERT(src->ndim == dst->ndim);
  ASSERT(src->data != NULL);
  ASSERT(dst->data != NULL);
  if (src->dtype.code == kDLUInt) ASSERT(dst->dtype.code == kDLUInt || dst->dtype.code == kDLInt);
  ASSERT(src->dtype.bits == dst->dtype.bits);
  ASSERT(src->dtype.lanes == dst->dtype.lanes);
  ASSERT(src->dtype.code != kDLComplex);
  ASSERT(src->dtype.code != kDLBfloat);
  ASSERT(src->dtype.lanes == 1);

  _dltensor_abs(dst, src);
}

static void __internal_copy_dltensor(DLTensor* dst, const DLTensor* src) {
  int    ndim      = src->ndim;
  size_t elem_size = dltensor_elem_size(src);
  if (dltensor_is_packed(src) && dltensor_is_packed(dst)) {
    // Use a single memcpy in case src and dst are packed.
    _memcpy(dst->data, src->data, dltensor_data_size(src));
  } else if (ndim == 1) {
    void*     p_src        = src->data;
    void*     p_dst        = dst->data;
    size_t    num_elements = src->shape[0];
    ptrdiff_t src_stride   = dltensor_bstride(src, 0);
    ptrdiff_t dst_stride   = dltensor_bstride(dst, 0);
    for (int i = 0; i < (int)num_elements; i++) {
      _memcpy(p_dst, p_src, elem_size);
      p_src += src_stride;
      p_dst += dst_stride;
    }
  } else if (ndim == 2) {
    // Deal with two dimensional views directly to avoid the overhead of recursion for tall and narrow matrices
    void*     p_src               = src->data;
    void*     p_dst               = dst->data;
    size_t    num_lines           = src->shape[0];
    size_t    num_pixels_per_line = src->shape[1];
    ptrdiff_t src_stride          = dltensor_bstride(src, 0);
    ptrdiff_t dst_stride          = dltensor_bstride(dst, 0);
    for (int y_idx = 0; y_idx < (int)num_lines; y_idx++) {
      _memcpy(p_dst, p_src, num_pixels_per_line * elem_size);
      p_src += src_stride;
      p_dst += dst_stride;
    }
  } else {
    // Use recursion to deal with more than two dimensions
    size_t num_subtensors = src->shape[0];
    for (int i = 0; i < (int)num_subtensors; i++) {
      dltensor_declare(sub_src, ndim - 1);
      dltensor_strip_dim(&sub_src, src, i);
      dltensor_declare(sub_dst, ndim - 1);
      dltensor_strip_dim(&sub_dst, dst, i);
      __internal_copy_dltensor(&sub_dst, &sub_src);
    }
  }
}

void dltensor_deep_copy(DLTensor* dst, const DLTensor* src) {
  ASSERT(src->ndim == dst->ndim);
  int ndim = src->ndim;
  ASSERT(dltensor_estride(src, ndim - 1) == 1);
  ASSERT(dltensor_estride(dst, ndim - 1) == 1);
  ASSERT(src->dtype.bits == dst->dtype.bits);
  ASSERT(src->dtype.code == dst->dtype.code);
  ASSERT(src->dtype.lanes == dst->dtype.lanes);
  for (int i = 0; i < ndim; i++) {
    ASSERT(src->shape[i] == dst->shape[i]);
  }
  __internal_copy_dltensor(dst, src);
}

bool dltensor_tile_iterate(const DLTensor* t, const dltensor_tile_params_t* params, DLTensor* tile_out, uint64_t x_idx,
                           uint64_t y_idx) {
  // ASSERT the output tensor has the correct number of dimensions and a non-NULL shapes and strides array
  ASSERT(tile_out->shape != NULL);
  ASSERT(tile_out->strides != NULL);
  ASSERT(tile_out->ndim == t->ndim);
  // ASSERT the x and y dimensions are within the tensor's shape
  ASSERT(params->x_dim < (uint64_t)t->ndim);
  ASSERT(params->y_dim < (uint64_t)t->ndim);
  // ASSERT the tile width and height are non-zero
  ASSERT(params->tile_width > 0);
  ASSERT(params->tile_height > 0);
  // ASSERT the tile stride is non-zero
  ASSERT(params->tile_x_stride > 0);
  ASSERT(params->tile_y_stride > 0);
  // ASSERT the tile offsets are within the tensor shape
  ASSERT(params->x_offset < (uint64_t)t->shape[params->x_dim]);
  ASSERT(params->y_offset < (uint64_t)t->shape[params->y_dim]);

  LOG_TRC("Extracting tile %d, %d from tensor", x_idx, y_idx);
  // Calculate the start and end indices of the tile in the x and y direction
  uint64_t x_start = x_idx * params->tile_x_stride + params->x_offset;
  uint64_t y_start = y_idx * params->tile_y_stride + params->y_offset;
  uint64_t x_end   = x_start + params->tile_width;
  uint64_t y_end   = y_start + params->tile_height;
  // Check if the tile is out of bounds
  if (x_start >= (uint64_t)t->shape[params->x_dim] || y_start >= (uint64_t)t->shape[params->y_dim]) {
    LOG_TRC("Tile out of bounds: %d, %d", x_start, y_start);
    return false;
  }
  // Crop the tile to the tensor's shape if it exceeds it
  dltensor_bbox_t t_bbox = dltensor_get_bbox_from_tensor(t, params->x_dim, params->y_dim);
  dltensor_bbox_t bbox   = {.x1 = x_start, .y1 = y_start, .x2 = x_end, .y2 = y_end};
  bbox                   = dltensor_get_bbox_intersect(t_bbox, bbox);
  // Calculate the slice parameters
  dltensor_slice_t slices[t->ndim];
  for (int i = 0; i < t->ndim; i++) {
    if ((uint64_t)i == params->x_dim) {
      slices[i].start = bbox.x1;
      slices[i].end   = bbox.x2;
      slices[i].step  = 1;
    } else if ((uint64_t)i == params->y_dim) {
      slices[i].start = bbox.y1;
      slices[i].end   = bbox.y2;
      slices[i].step  = 1;
    } else {
      slices[i].start = 0;
      slices[i].end   = t->shape[i];
      slices[i].step  = 1;
    }
  }
  LOG_TRC("Extracting tile with bbox %d, %d, %d, %d", bbox.x1, bbox.y1, bbox.x2, bbox.y2);
  // Extract the tile
  dltensor_slice(t, tile_out, slices);
  return true;
}
