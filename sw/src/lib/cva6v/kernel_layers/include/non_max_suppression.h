// Description: Header file for non max suppression kernel
// Owner: Domenic Wuethrich <domenic.wuethrich@axelera.ai>

#pragma once

#include <stdint.h>

#define MAX(x, y) (((x) > (y)) ? (x) : (y))
#define MIN(x, y) (((x) < (y)) ? (x) : (y))
#define ABS(x)    ((x < 0) ? (-x) : x)

// Calculate the intersection area over the union area
float iou(int32_t *box0, int32_t *box1);

// Calculate the intersection area over the union area
void iou_rvv(int32_t *box0, int32_t *boxes, uint32_t *indexes, uint32_t num_boxes, float *ious);

// Apply non maximum suppression to a set of detected boxes. This
// function choses the best fitting boxe for every object recognized
// and removes all others.
// Output: nms_indices: a set of chosen indices of the input boxes
uint32_t non_max_suppression(int32_t *boxes, uint32_t num_boxes, uint32_t *class, _Float16 *scores,
                             _Float16 score_threshold, _Float16 nms_threshold, uint32_t *nms_indices);

// Apply non maximum suppression to a set of detected boxes. This
// function choses the best fitting boxe for every object recognized
// and removes all others.
// Output: nms_indices: a set of chosen indices of the input boxes
uint32_t non_max_suppression_rvv(int32_t *boxes, uint32_t num_boxes, uint32_t *class, _Float16 *scores,
                                 _Float16 score_threshold, _Float16 nms_threshold, uint32_t *nms_indices);
