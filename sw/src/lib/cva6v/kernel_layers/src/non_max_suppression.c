// Description: Non maximum suppression kernel
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#include <non_max_suppression.h>
#include <math.h>
#include <riscv_vector.h>
#include <stdbool.h>

void iou_rvv(int32_t *box0, int32_t *boxes, uint32_t *indexes, uint32_t num_boxes, float *ious) {
  while (num_boxes > 0) {
    uint32_t    vl = __riscv_vsetvl_e32m2(num_boxes);
    vuint32m2_t idxs;
    idxs             = __riscv_vle32_v_u32m2(indexes, vl);
    idxs             = __riscv_vmul_vx_u32m2(idxs, 16, vl);
    vint32m2x4_t seg = __riscv_vluxseg4ei32_v_i32m2x4(boxes, idxs, vl);
    vint32m2_t   x1  = __riscv_vget_v_i32m2x4_i32m2(seg, 0);
    vint32m2_t   y1  = __riscv_vget_v_i32m2x4_i32m2(seg, 1);
    vint32m2_t   x2  = __riscv_vget_v_i32m2x4_i32m2(seg, 2);
    vint32m2_t   y2  = __riscv_vget_v_i32m2x4_i32m2(seg, 3);
    vint32m2_t   ix1 = __riscv_vmax_vx_i32m2(x1, box0[0], vl);
    vint32m2_t   ix2 = __riscv_vmin_vx_i32m2(x2, box0[2], vl);
    vint32m2_t   iy1 = __riscv_vmax_vx_i32m2(y1, box0[1], vl);
    vint32m2_t   iy2 = __riscv_vmin_vx_i32m2(y2, box0[3], vl);

    vint32m2_t w = __riscv_vmax_vx_i32m2(__riscv_vsub_vv_i32m2(ix2, ix1, vl), 0, vl);
    vint32m2_t h = __riscv_vmax_vx_i32m2(__riscv_vsub_vv_i32m2(iy2, iy1, vl), 0, vl);

    vint32m2_t   area_inter  = __riscv_vmul_vv_i32m2(w, h, vl);
    vfloat32m2_t farea_inter = __riscv_vfcvt_f_x_v_f32m2(area_inter, vl);

    uint32_t     area_box0   = (box0[2] - box0[0]) * (box0[3] - box0[1]);
    vint32m2_t   diffx       = __riscv_vsub_vv_i32m2(x2, x1, vl);
    vint32m2_t   diffy       = __riscv_vsub_vv_i32m2(y2, y1, vl);
    vint32m2_t   area_boxes  = __riscv_vmul_vv_i32m2(diffx, diffy, vl);
    vint32m2_t   area_union  = __riscv_vsub_vv_i32m2(__riscv_vadd_vx_i32m2(area_boxes, area_box0, vl), area_inter, vl);
    vfloat32m2_t farea_union = __riscv_vfcvt_f_x_v_f32m2(area_union, vl);
    vfloat32m2_t iou_        = __riscv_vfmul_vv_f32m2(farea_inter, __riscv_vfrec7_v_f32m2(farea_union, vl), vl);
    __riscv_vse32_v_f32m2(ious, iou_, vl);

    num_boxes -= vl;
    indexes   += vl;
    ious      += vl;
  }
}

float iou(int32_t *box0, int32_t *box1) {
  int32_t x1 = MAX(box0[0], box1[0]);
  int32_t x2 = MIN(box0[2], box1[2]);
  int32_t y1 = MAX(box0[1], box1[1]);
  int32_t y2 = MIN(box0[3], box1[3]);

  uint32_t w = MAX(0, x2 - x1);
  uint32_t h = MAX(0, y2 - y1);

  uint32_t area_inter = w * h;

  uint32_t area_box0 = (box0[2] - box0[0]) * (box0[3] - box0[1]);
  uint32_t area_box1 = (box1[2] - box1[0]) * (box1[3] - box1[1]);

  float iou = (float)area_inter / (float)(area_box0 + area_box1 - area_inter);

  return iou;
}

uint32_t non_max_suppression(int32_t *boxes, uint32_t num_boxes, uint32_t *class, _Float16 *scores,
                             _Float16 score_threshold, _Float16 nms_threshold, uint32_t *nms_indices) {
  if (num_boxes == 0) {
    return 0;
  }

  // Filter out indices with a scores lower than threshold
  uint32_t num_indices = 0;
  uint32_t indices[num_boxes];
  for (uint32_t i = 0; i < num_boxes; i++) {
    if (scores[i] >= score_threshold) {
      indices[num_indices++] = i;
    }
  }

  // Sort indices by corresponding scores (descending)
  for (uint32_t i = 0; i < num_indices; i++) {
    for (uint32_t j = i + 1; j < num_indices; j++) {
      if (scores[indices[i]] < scores[indices[j]]) {
        uint32_t tmp = indices[i];
        indices[i]   = indices[j];
        indices[j]   = tmp;
      }
    }
  }

  uint32_t _num_indices    = 0;
  uint32_t num_nms_indices = 0;
  while (num_indices > 0) {
    uint32_t current_indice        = indices[0];
    nms_indices[num_nms_indices++] = current_indice;
    for (uint32_t i = 1; i < num_indices; i++) {
      uint32_t compare_indice = indices[i];
      float    _iou           = iou(boxes + current_indice * 4, boxes + compare_indice * 4);
      if (class[current_indice] == class[compare_indice] && _iou > (float)nms_threshold) {
        continue;
      } else {
        indices[_num_indices++] = compare_indice;
      }
    }
    num_indices  = _num_indices;
    _num_indices = 0;
  }

  return num_nms_indices;
}

uint32_t non_max_suppression_rvv(int32_t *boxes, uint32_t num_boxes, uint32_t *class, _Float16 *scores,
                                 _Float16 score_threshold, _Float16 nms_threshold, uint32_t *nms_indices) {
  if (num_boxes == 0) {
    return 0;
  }

  // Filter out indices with a scores lower than threshold
  uint32_t num_indices = 0;
  uint32_t indices[num_boxes];
  for (uint32_t i = 0; i < num_boxes; i++) {
    if (scores[i] >= score_threshold) {
      indices[num_indices++] = i;
    }
  }

  // Sort indices by corresponding scores (descending)
  for (uint32_t i = 0; i < num_indices; i++) {
    for (uint32_t j = i + 1; j < num_indices; j++) {
      if (scores[indices[i]] < scores[indices[j]]) {
        uint32_t tmp = indices[i];
        indices[i]   = indices[j];
        indices[j]   = tmp;
      }
    }
  }

  uint32_t _num_indices    = 0;
  uint32_t num_nms_indices = 0;
  while (num_indices > 0) {
    uint32_t current_indice        = indices[0];
    nms_indices[num_nms_indices++] = current_indice;

    float ious[num_indices - 1];
    iou_rvv(boxes + 4 * current_indice, boxes, indices + 1, num_indices - 1, ious);
    for (uint32_t i = 1; i < num_indices; i++) {
      uint32_t compare_indice = indices[i];
      if (class[current_indice] == class[compare_indice] && ious[i - 1] > (float)nms_threshold) {
        continue;
      } else {
        indices[_num_indices++] = compare_indice;
      }
    }
    num_indices  = _num_indices;
    _num_indices = 0;
  }

  return num_nms_indices;
}
