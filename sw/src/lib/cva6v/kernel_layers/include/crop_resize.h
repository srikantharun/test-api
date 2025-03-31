// Description: Header file for crop_resize kernel
// Owner: Michael Platzer <michael.platzer@axelera.ai>

#pragma once

#include <stdint.h>

void crop_resize_rvv(const uint8_t *src, uint8_t *dst, long h, long w, long c, long rsz_h, long rsz_w,
                     long crp_h, long crp_w);
