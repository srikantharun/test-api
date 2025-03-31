// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DLPack utility functions
// Owner: Michael Platzer <michael.platzer@axelera.ai>

#pragma once

#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>

#include <dlpack.h>
#include <log.h>
#include <printf.h>
#include <testutils.h>

/**
 * Get the data size of the dltensor's memory container in bytes.
 *
 * The size is calculated according to the snippet provided in the DLPack's documentation:
 * https://dmlc.github.io/dlpack/latest/c_api.html#_CPPv4N8DLTensor4dataE
 *
 * @param t The tensor for which to report the size
 * @return size_t The size of the tensors data* field in unit bytes
 */
static inline size_t dltensor_data_size(const DLTensor *t) {
  size_t size = 1;
  for (int64_t i = 0; i < t->ndim; ++i) {
    size *= t->shape[i];
  }
  size *= (t->dtype.bits * t->dtype.lanes + 7) / 8;
  return size;
}

/**
 * Get the element size in bytes of one element of a DLTensor.
 *
 * The size is calculated as outlined in the DLPack documentation of DLTensor:
 * https://dmlc.github.io/dlpack/latest/c_api.html#_CPPv4N8DLTensor4dataE
 *
 * @param[in] t Input tensor.
 * @return      Size in bytes of one element of `t`.
 */
static inline size_t dltensor_elem_size(const DLTensor *t) { return (t->dtype.bits * t->dtype.lanes + 7ull) / 8ull; }

/**
 * Get the byte stride of dimension `dim` of a DLTensor.
 *
 * The byte stride is calculated by multiplying the element size of the tensor with the specified
 * element stride of the respective dimension, or by calculating the stride assuming compact row-
 * major order if the tensor's `strides` field is `NULL`, as outlined in the DLPack documentation:
 * https://dmlc.github.io/dlpack/latest/c_api.html#_CPPv4N8DLTensor4dataE
 *
 * @param[in] t   Input tensor.
 * @param[in] dim Index of the dimension for which the byte stride shall be returned.
 * @return        Byte stride of the desired dimension of `t` or -1 if `t` has no dimension `dim`.
 */
static inline int64_t dltensor_bstride(const DLTensor *t, int dim) {
  if (dim < 0 || dim >= t->ndim) {
    return -1;
  }
  int64_t bstride = dltensor_elem_size(t);
  if (t->strides != NULL) {
    bstride *= t->strides[dim];
  } else {
    for (int64_t i = dim + 1; i < t->ndim; i++) {
      bstride *= t->shape[i];
    }
  }
  return bstride;
}

/**
 * Get the element stride of dimension `dim` of a DLTensor.
 *
 * If the given tensor's strides field is non-`NULL`, we directly return the
 * relevant value from it. If `strides` is `NULL` the tensor is considered
 * packed, as outlined in the DLPack documentation. In this case we calculate
 * the element stride by multiplying all shape values of larger dimensions
 * together.
 *
 * This is basically a convenience function that allows to obtain element
 * strides regardless whether the dltensor contains a strides array or not.
 *
 * @param[in] t Input tensor.
 * @param[in] dim Index of the dimension for which the element stride shall be returned.
 * @return Element strite of the desired dimension of `t` or -1 if `t` has no dimension `dim`.
 */
static inline int64_t dltensor_estride(const DLTensor *t, int dim) {
  if (dim < 0 || dim >= t->ndim) {
    return -1;
  }
  if (t->strides != NULL) {
    return t->strides[dim];
  } else {
    int64_t estride = 1;
    for (int64_t i = dim + 1; i < t->ndim; i++) {
      estride *= t->shape[i];
    }
    return estride;
  }
}

/**
 * Returns true if the given DLTensor is in packed format.
 *
 * If the tensor has its stride field set to NULL, the DLTensor is packed by
 * definition and the function returns 0. If strides != NULL, the function will
 * check each entry in the strides field to verify the DLTensor is packed and
 * thus the strides field could be set to NULL.
 *
 * @param t The tensor to check.
 * @return true If the tensor is in packed row-major format
 * @return false Otherwise
 */
bool dltensor_is_packed(const DLTensor *t);

/**
 * Returns the number of packed tensors of the given DLTensor instance.
 *
 * @param t
 * @return int The number of dimensions that are packed
 */
int dltensor_get_num_packed_dims(const DLTensor *t);

/**
 * Strip dimension 0 (i.e., the highest or outer dimension) off a DLTensor, yielding the sub-tensor
 * at index `idx` of that dimension.
 *
 * @param[out] dst Destination tensor structure that receives the extracted sub-tensor.
 * @param[in]  src Input tensor.
 * @param[in]  idx Index at which the sub-tensor should be extracted of `src`.
 * @return         0 on success, otherwise -1 if the source tensor has no dimensions or `idx` is
 *                 out-of-bounds.
 */
static inline int dltensor_strip_dim(DLTensor *restrict dst, const DLTensor *restrict src, int idx) {
  if (src->ndim <= 0 || idx < 0 || idx >= src->shape[0]) {
    return -1;
  }
  dst->data        = ((uint8_t *)src->data) + dltensor_bstride(src, 0) * idx;
  dst->device      = src->device;
  dst->ndim        = src->ndim - 1;
  dst->dtype       = src->dtype;
  dst->shape       = src->shape + 1;
  dst->strides     = src->strides != NULL ? src->strides + 1 : NULL;
  dst->byte_offset = src->byte_offset;
  return 0;
}

/**
 * Returns a pointer to the element at given index within data.
 *
 * E.g. `my_tensor.dltensor_index(&my_tensor, 2,4,4)]` would return element
 * "my_tensor[2,4,4]" in a framework like numpy.
 *
 * Important: You must supply exactly as many indices as there are dimensions
 * and each index argument must be of type int32_t and not int64_t! This is a
 * limitation of variadic functions. If we declared it int64_t, supplying an
 * integer literal without the proper int64 suffix (e.g. `1920ll`) would cause a
 * very hard to find bug since the function would read 8 bytes from the stack
 * and interpret them as int64 although only 4 were actually supplied.
 *
 * @param tensor Tensor to index into
 * @return The void pointer into the data buffer at the given index.
 */
static inline void *dltensor_index(const DLTensor *tensor, ...) {
  va_list ap;
  va_start(ap, tensor);
  int64_t idx       = tensor->byte_offset;
  size_t  elem_size = dltensor_elem_size(tensor);
  for (int64_t i = 0; i < tensor->ndim; i++) {
    int32_t cur_idx = va_arg(ap, int);
    if (tensor->strides == NULL) {
      idx += cur_idx * dltensor_bstride(tensor, i) / elem_size;
    } else {
      idx += cur_idx * tensor->strides[i];
    }
  }
  va_end(ap);
  return tensor->data + idx * elem_size;
}

/**
 * A slice struct to be used with DLTensorSliceView. All out-of-range start end
 * values are clamped to be within range. Reverse slices are supported by
 * specifying a negative step and the index clamping logic takes the slice
 * direction into account. However, beware that in this case, start must be
 * larger than end and is *exclusive*.
 * E.g. start=4, end=1, step=1 yields an empty tensor.
 * and start=4, end=0, step=-1 yields elements (3, 2, 1, 0) in order.
 */
typedef struct {
  /*! The element start idx (always inclusive).*/
  int64_t start;
  /*! The element end idx (always exclusive).*/
  int64_t end;
  /*! The step size.*/
  int64_t step;
} dltensor_slice_t;

/**
 * Generates a new slice view of tensor_in
 *
 * The slices array must have tensor_in.ndim length and specifies the slicing
 * pattern for each of the input dimensions. The implementation supports
 * negative slices (slicing in the reverse direction, specified with a negative
 * step size), but out of bound access DO NOT wrap around but are clamped. The
 * result is written to slice_out which is another DLTensor pointing to the same
 * memory but with appropriately offseted data pointer, shapes and strides (to
 * account step-size larger than 1).
 *
 * @param tensor_in
 * @param slice_out
 * @param slices
 */
static inline void dltensor_slice(const DLTensor *tensor_in, DLTensor *slice_out, const dltensor_slice_t *slices) {
  ASSERT(slice_out->strides != NULL);
  ASSERT(slice_out->shape != NULL);
  slice_out->ndim        = tensor_in->ndim;
  slice_out->data        = tensor_in->data;
  slice_out->byte_offset = tensor_in->byte_offset;
  slice_out->dtype       = tensor_in->dtype;
  slice_out->device      = tensor_in->device;
  uint64_t curr_stride   = 1;
  for (int64_t i = tensor_in->ndim - 1; i >= 0; i--) {
    int64_t start_idx;
    int64_t end_idx;
    if (slices[i].step > 0) {
      start_idx = (slices[i].start < 0) ? 0 : slices[i].start;
      end_idx   = (slices[i].end > tensor_in->shape[i]) ? tensor_in->shape[i] : slices[i].end;
    } else {
      end_idx   = (slices[i].end < -1) ? -1 : slices[i].end;
      start_idx = (slices[i].start > tensor_in->shape[i] - 1) ? tensor_in->shape[i] - 1 : slices[i].start;
    }
    // If the input tensor's strides array is NULL we have a compact tensor and
    // we thus must calculate the correct strides on the fly (factorial over all
    // shape[k] with k > i)
    if (tensor_in->strides != NULL) {
      slice_out->strides[i] = tensor_in->strides[i];
    } else {
      slice_out->strides[i] = curr_stride;
      curr_stride           *= tensor_in->shape[i];
    }
    slice_out->data       += start_idx * slice_out->strides[i] * dltensor_elem_size(tensor_in);
    slice_out->strides[i] *= slices[i].step;
    int64_t new_shape     = (end_idx - start_idx) / slices[i].step;
    new_shape             = (new_shape >= 0) ? new_shape : 0;
    slice_out->shape[i]   = new_shape;
    // printf("start_idx: %d, end_idx: %d, step: %d, stride: %d, shape: %d\n", start_idx, end_idx, slices[i].step,
    // slice_out->strides[i], slice_out->shape[i]);
  }
}

/**
 * A utility data structure to store indices coordinates of 2D bounding boxes.
 *
 */
typedef struct {
  uint64_t x1;
  uint64_t y1;
  uint64_t x2;
  uint64_t y2;
} dltensor_bbox_t;

/**
 * Get the intersection of box `a` and `b`.
 *
 * If the two boxes do not intersect, the result is an ROI object with the all
 * zeroes (x1=y1=x2=y2=0).
 *
 * @param a
 * @param b
 * @return tensor_roi_t The intersection coordinate of `a` and `b` or the all
 * zero bbox if the intersect is empty.
 */
static inline dltensor_bbox_t dltensor_get_bbox_intersect(dltensor_bbox_t a, dltensor_bbox_t b) {
  dltensor_bbox_t result;
  result.x1 = (a.x1 > b.x1) ? a.x1 : b.x1;
  result.x2 = (a.x2 < b.x2) ? a.x2 : b.x2;
  result.y1 = (a.y1 > b.y1) ? a.y1 : b.y1;
  result.y2 = (a.y2 < b.y2) ? a.y2 : b.y2;
  if ((result.x1 >= result.x2) | (result.y1 >= result.y2)) {
    result.x1 = 0;
    result.x2 = 0;
    result.y1 = 0;
    result.y2 = 0;
  }
  return result;
}

/**
 * Return a new bbox struct that captures the outline of the given DLTensor `t`.
 * `x_dim` and `y_dim` denote the index of the dimensions to be considered as x-
 * and y-axis respectively. If either of the two dimension indices is out of
 * range, the function will return the empty bbox (bbox with coordinates all
 * zero.) .
 *
 * @param t
 * @param x_dim
 * @param y_dim
 * @return dletensor_bbox_t
 */
static inline dltensor_bbox_t dltensor_get_bbox_from_tensor(const DLTensor *t, int x_dim, int y_dim) {
  dltensor_bbox_t result;
  if (x_dim < 0 || x_dim > t->ndim || y_dim < 0 || y_dim > t->ndim) {
    result.x1 = 0;
    result.x2 = 0;
    result.y1 = 0;
    result.y2 = 0;
  } else {
    result.x1 = 0;
    result.x2 = t->shape[x_dim];
    result.y1 = 0;
    result.y2 = t->shape[y_dim];
  }
  return result;
}

/**
 * Helper macro for 2D-tiled processing. The macro declares a new tensor with
 * name `out_name` that is pointing to a rectangular view of input tensor `in`.
 *
 * The view's rectangular outline is specified with the p_bbox parameter (a
 * pointer to a dltensor_bbox_t struct). The macro will first legalize the given
 * bbox to be fully contained within the limits of the input tensor and
 * overwrite the input bbox with the legalized coordinates. Then it declares a
 * new DLTensor struct called `out_name` and uses the dltensor_slice function to
 * initialize it with a rectangular view within p_in (thus pointing to the same
 * data underneath using a different start pointer and strides).
 *
 * @param p_in *DLTensor The pointer to the dltensor struct on which we want to
 * obtain the view.
 * @param out_name The symbolic name to use fo the new dltensor struct
 * containing the view.
 * @param p_bbox[in/out] *dltensor_bbox_t The start (x1/y1) and end (x2/y2,
 * exclusive) indices to use for the view.
 * @param x_dim int The index of the dimension of `p_in` to consider the x-axis.
 * @param y_dim int The index of the dimension of `p_in` to consider the y-axis.
 */
#define dltensor_cropped_view(p_in, out_name, p_bbox, x_dim, y_dim)                                      \
  dltensor_declare(out_name, (p_in)->ndim) {                                                             \
    dltensor_bbox_t __bbox =                                                                             \
        dltensor_get_bbox_intersect(dltensor_get_bbox_from_tensor((p_in), (x_dim), (y_dim)), *(p_bbox)); \
    dltensor_slice_t slices[(p_in)->ndim];                                                               \
    for (int64_t i = 0; i < (p_in)->ndim; i++) {                                                         \
      if (i == (x_dim)) {                                                                                \
        slices[i].start = __bbox.x1;                                                                     \
        slices[i].end   = __bbox.x2;                                                                     \
        slices[i].step  = 1;                                                                             \
      } else if (i == (y_dim)) {                                                                         \
        slices[i].start = __bbox.y1;                                                                     \
        slices[i].end   = __bbox.y2;                                                                     \
        slices[i].step  = 1;                                                                             \
      } else {                                                                                           \
        slices[i].start = 0;                                                                             \
        slices[i].end   = (p_in)->shape[i];                                                              \
        slices[i].step  = 1;                                                                             \
      }                                                                                                  \
    }                                                                                                    \
    dltensor_slice((p_in), &out_name, slices);                                                           \
    (p_bbox)->x1 = __bbox.x1;                                                                            \
    (p_bbox)->y1 = __bbox.y1;                                                                            \
    (p_bbox)->x2 = __bbox.x2;                                                                            \
    (p_bbox)->y2 = __bbox.y2;                                                                            \
  }

/**
 * Helper macro to quickly define a new DLTensor with a given dimensionality.
 * Besides declaring a new DLTensor variable with the name `name` it also
 * declares two arrays for stride and shapes with the name `name_strides` and
 * `name_shape`. The shape is initialized with the provided dimensions (variadic
 * macro argument) and the strides are initialized to packed row-major memory
 * layout (equivalent to `.strides==NULL` but explicitly set to allow stride
 * modification). The dltensor is finally initialized with the arguments, where
 * _data is a pointer to the backing buffer to use (must be of type `(void*)`) and
 * _dtype (`DLDataType`) is the dtype to use.
 *
 */
#define dltensor_define(name, _ndim, _data, _dtype, ...)        \
  int64_t  name##_shape[_ndim] = {__VA_ARGS__};                 \
  uint64_t name##_strides[_ndim];                               \
  {                                                             \
    int64_t strides = ((_dtype).bits * (_dtype).lanes + 7) / 8; \
    for (int64_t i = (_ndim)-1; i >= 0; i--) {                  \
      name##_strides[i] = strides;                              \
      strides           *= name##_shape[i];                     \
    }                                                           \
  }                                                             \
  DLTensor name = {.ndim        = _ndim,                        \
                   .data        = _data,                        \
                   .dtype       = _dtype,                       \
                   .shape       = name##_shape,                 \
                   .strides     = name##_strides,               \
                   .byte_offset = 0};

/**
 * Declares a shapes and strides array of the given dimensionality and finally
 * declares a tensor with ndim, shape and strides initialized but everything
 * else left uninitialized.
 *
 * Mainly useful to create slices into existing dltensors with the
 * dltensor_slice function.
 *
 */
#define dltensor_declare(name, _ndim) \
  int64_t  name##_shape[_ndim];       \
  int64_t  name##_strides[_ndim];     \
  DLTensor name = {.ndim = _ndim, .data = NULL, .shape = name##_shape, .strides = name##_strides};

/**
 * Defines a packed tensor (strides = NULL) with `ndim` dimensions, sets its
 * data buffer to `data` and initializes the shape with the given dimensions
 * (variadic argument). E.g. `dltensor_declare_packed(my_tensor, 3, &buff, 1920,
 * 1080, 3)` would declare a packed tensor named `my_tensor` with 3 dimensions,
 * its data field set to `buff` and  its shape array already initialized with
 * {1920, 1080, 3}.
 *
 */
#define dltensor_define_packed(name, _ndim, _data, _dtype, ...) \
  int64_t  name##_shape[_ndim] = {__VA_ARGS__};                 \
  DLTensor name                = {                              \
                     .ndim = _ndim, .data = _data, .dtype = _dtype, .shape = name##_shape, .strides = NULL, .byte_offset = 0};

/**
 * Defines a packed tensor (strides = NULL) with `ndim` dimensions that is
 * backed by _buff. The tensor will have a dtype of uint8_t and a shape of
 * [sizeof(_buf), 1, 1, 1 ...] (depending on number of dimensions). This is
 * useful for functions that generate an output tensor whose dimension is
 * upper-bounded but not a-priori known.
 */
#define dltensor_define_buffer(name, _buff, _ndim)                      \
  int64_t name##_shape[_ndim];                                          \
  name##_shape[0] = sizeof(_buff);                                      \
  for (int64_t i = 1; i < _ndim; i++) name##_shape[i] = 1;              \
  DLTensor name = {.ndim    = _ndim,                                    \
                   .data    = _buff,                                    \
                   .dtype   = {.code = kDLUInt, .bits = 8, .lanes = 1}, \
                   .shape   = name##_shape,                             \
                   .strides = NULL}

/**
 * Creates a new tensor with the given name, number of dimensions, data pointer
 * and dtype. A shapes and strides array is declared with the name `name_shape`
 * and `name_strides` respectively and the respective fields of the tensor are set.
 * However, the strides and shapes are left uninitialized and must be set manually
 * after the tensor has been declared.
 *
 */
#define DLTENSOR_CREATE(name, _ndim, _data, _dtype) \
  int64_t  name##_shape[_ndim];                     \
  int64_t  name##_strides[_ndim];                   \
  DLTensor name = {.ndim = _ndim, .data = _data, .dtype = _dtype, .shape = name##_shape, .strides = name##_strides};

/**
 * Pretty print the given tensor. Emitting dtype, shape, and data.
 *
 * The linereak_dim parameter controls above which dimensions linebreaks are
 * added. E.g. for a packed RGB (HWC-ordering) tensor, you might want to display
 * a 2d tensor of packed 3-element groups instead of printing stacked wx3
 * tensors. Therefore, you would use linebreak_dim = 2. For a 2d tensor, a
 * linebreak dimension of 0 would cause the tensor to be printed as a very tall
 * column vector (still including the proper brace nesting). With a
 * linebreak_dim of 1, the tensor prints as a normal 2d matrix while a
 * linebreak_dim would cause it to be printed on a single line.
 *
 * @param tensor The tensor to print
 * @param linebreak_dim The dimension above which add line breaks after every
 * sub tensor.
 */
void dltensor_print(const DLTensor *tensor, int linebreak_dim);

/**
 * Same as dltensor_print, but uses the logging facility to conditionally print
 * the tensor depending on the current logging level.
 *
 * In contrast to the log_info, log_debug, etc. logging functions, calls to this
 * functions are NOT optimized away if the minimum logging level is raised
 * (-DLOG_MIN_LEVEL). Keep this in mind when optimizing your code!
 *
 * @param log_level The logging level at which to print the tensor.
 * @param tensor The tensor to print
 * @param linebreak_dim The dimension above which add line breaks after every
 * sub tensor.
 */
void dltensor_logprint(int log_level, const DLTensor *tensor, int linebreak_dim);

/**
 * Debugging function to print metadata about the tensor (without its actual content) to stdout.
 *
 * @param tensor
 */
void dltensor_info(const DLTensor *tensor);

/**
 * Debugging function to print a slice on two dimension of a given tensor.
 *
 * @param _log_level The log level to use for printing.
 * @param p_tensor A pointer to a tensor for which to print a slice.
 * @param _line_break_dim The dimension on which to insert line breaks (see `dltensor_print` for details).
 * @param _x_dim The index of the dimension of `p_tensor` that should be considered the x-dimension.
 * @param _y_dim The index of the dimension of `p_tensor` that should be considered the y-dimension.
 * @param _x1 Upper left corner's x-index of the rectangular slice view to print (x-dim slice start, inclusive).
 * @param _x2 Lower right corner's x-index of the rectangular slice view to print (x-dim slice end, exclusive).
 * @param _y1 Upper left corner's y-index of the rectangular slice view to print (y-dim slice start, inclusive).
 * @param _y2 Lower right corner's y-index of the rectangular slice view to print (y-dim slice end, exclusive).
 *
 */
#define dltensor_logprint_tile(_log_level, p_tensor, _line_break_dim, _x_dim, _y_dim, _x1, _x2, _y1, _y2)            \
  {                                                                                                                  \
    dltensor_bbox_t __bbox2 = {.x1 = (_x1), .y1 = (_y1), .x2 = (_x2), .y2 = (_y2)};                                  \
    dltensor_cropped_view((p_tensor), __view, &(__bbox2), (_x_dim), (_y_dim));                                       \
    IMPL_LOG(_log_level,  "Slice x=%d:%d, y=%d:%d of tensor:", (_x1), (_x2), (_y1), (_y2))                           \
    dltensor_loginfo((_log_level), (p_tensor));                                                                      \
    IMPL_LOG(_log_level,  "slice view: ")                                                                            \
    dltensor_logprint((_log_level), &__view, (_line_break_dim));                                                     \
  }

/**
 * Same as dltensor_info, but uses the logging facility to conditionally print
 * the tensor metadata depending on the current logging level.
 *
 * In contrast to the log_info, log_debug, etc. logging functions, calls to this
 * functions are NOT optimized away if the minimum logging level is raised
 * (-DLOG_MIN_LEVEL). Keep this in mind when optimizing your code!
 *
 * @param log_level The logging level at which to print the tensor metadata.
 * @param tensor The tensor for which to print it's metadata
 */
void dltensor_loginfo(int log_level, const DLTensor *tensor);

static inline void dltensor_shallow_copy(const DLTensor *src, DLTensor *dst) {
  ASSERT(dst->shape != NULL);
  if (src->strides != NULL) {
    ASSERT(dst->strides != NULL);
  }
  dst->byte_offset = src->byte_offset;
  dst->data        = src->data;
  dst->device      = src->device;
  dst->dtype       = src->dtype;
  dst->ndim        = src->ndim;
  for (int64_t i = 0; i < src->ndim; i++) {
    dst->shape[i] = src->shape[i];
  }
  if (src->strides) {
    for (int i = 0; i < src->ndim; i++) {
      dst->strides[i] = src->strides[i];
    }
  }
}

/**
 * Calculates the mean-squared-error between tensor a and b.
 *
 * The function does not support kComplex, kBFloat nor vectorized data type.
 *
 * @param a
 * @param b
 * @return double
 */
float dltensor_mse(const DLTensor *a, const DLTensor *b);

/**
 * Returns the maximum value within the flat tensor
 *
 * The function does not support kComplex, kBFloat nor vectorized data type.
 *
 * @param t
 * @return double
 */
float dltensor_max(const DLTensor *t);

/**
 * Calculates the peak-signal-to-noise ratio between reference tensor `ref` and its noisy version `noisy`.
 *
 * The function does not support kComplex, kBFloat nor vectorized data type.
 *
 * @param ref
 * @param noisy
 * @return double psnr[dB] or INFINITY if the error between a and b is 0.
 */
float dltensor_psnr(const DLTensor *ref, const DLTensor *noisy);

/**
 * Calculates elementwise a - b and stores the result in dst. Dst is allowed to alias to a or b.
 *
 * @param dst
 * @param a
 * @param b
 */
void dltensor_sub(DLTensor *dst, const DLTensor *a, const DLTensor *b);

/**
 * Calculates the absolute value of each element and stores it in dst. Dst is allowed to alias to src.
 *
 * @param dst
 * @param src
 */
void dltensor_abs(DLTensor *dst, const DLTensor *src);

/**
 * Returns the sum of all values within the flat tensor
 *
 * The function does not support kComplex, kBFloat nor vectorized data type.
 *
 * @param t
 * @return double
 */
float dltensor_sum(const DLTensor *t);

/**
 * Deep copies the data from src to dst.
 *
 * Both tensors must have the same datatype and shape but could have different
 * strides. The implementation contains optimized code paths to deal with packed
 * tensors more efficiently. Internally, the function makes use of calls to
 * memcpy to accelerate the copying of the data.
 *
 * @param dst
 * @param src
 */
void dltensor_deep_copy(DLTensor *dst, const DLTensor *src);

typedef struct {
  uint64_t x_dim;
  uint64_t y_dim;
  uint64_t tile_width;
  uint64_t tile_height;
  uint64_t tile_x_stride;
  uint64_t tile_y_stride;
  uint64_t x_offset;
  uint64_t y_offset;
} dltensor_tile_params_t;

/**
 * @brief Return the number of tiles that can be extracted from tensor `t` with
 * the given parameters in the x-direction.
 *
 * @param t
 * @param params
 * @return uint64_t
 */
static inline uint64_t dltensor_tile_x_count(const DLTensor *t, const dltensor_tile_params_t *params) {
  return (t->shape[params->x_dim] - params->x_offset + params->tile_x_stride - 1) / params->tile_x_stride;
}

/**
 * @brief Return the number of tiles that can be extracted from tensor `t` with
 * the given parameters in the y-direction.
 *
 * @param t
 * @param params
 * @return uint64_t
 */
static inline uint64_t dltensor_tile_y_count(const DLTensor *t, const dltensor_tile_params_t *params) {
  return (t->shape[params->y_dim] - params->y_offset + params->tile_y_stride - 1) / params->tile_y_stride;
}

/**
 * @brief Return subviews (tiles) of tensor `t` tiled across two dimensions.
 *
 * The function will iterate over the tensor `t` and extract tiles of size
 * `tile_width` x `tile_height` with a stride of `tile_x_stride` and
 * `tile_y_stride` in the x and y direction respectively. The dimensions `x_dim`
 * and `y_dim` specify the dimensions of the tensor to be considered as x- and
 * y-axis. Given the tile indices x_idx and y_idx, the function will return
 * views of the tensor `t` in `tile_out` (which must contain a shapes and
 * strides array of t.ndim dimensions). If the x_idx and/or y_idx are out of
 * bounds, the function will return false.
 *
 * The returned tiles might be smaller than `tile_width` x `tile_height` if the
 * tensor's shape is not a multiple of the tile size. In this case, the function
 * will return a tile with its actual shape cropped to the 'legal' content of
 * the source tensor t.
 *
 * @param t
 * @param params
 * @param tile_out
 * @param x_idx
 * @param y_idx
 * @return true if the tile was successfully extracted, false if either x_idx or
 * y_idx are out of bounds.
 */
bool dltensor_tile_iterate(const DLTensor *t, const dltensor_tile_params_t *params, DLTensor *tile_out, uint64_t x_idx,
                           uint64_t y_idx);
