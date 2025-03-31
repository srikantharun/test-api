// Description: Header file for color space conversion kernel
// Owner: Domenic Wüthrich <domenic.wuethrich@axelera.ai>

#pragma once

#include <stdint.h>

enum cspace_conversion { YUV2RGB, YCC2RGB, YUV2GRAY, RGB2YUV, RGB2YCC, RGB2GRAY };

typedef float           cspace_constants[5][3];
// Coefficients taken from https://docs.opencv.org/3.4/de/d25/imgproc_color_conversions.html#color_convert_rgb_ycrcb
// and https://web.archive.org/web/20180421030430/http://www.equasys.de/colorconversion.html
static cspace_constants ycc2rgb_constants = {{1.000, 0.000, 1.402},
                                             {1.000, -0.344, -0.714},
                                             {1.000, 1.772, 0.000},
                                             {0.000, 128.0, 128.0},
                                             {0.000, 0.000, 0.000}};
static cspace_constants yuv2rgb_constants = {{1.000, 0.000, 1.140},
                                             {1.000, -0.395, -0.581},
                                             {1.000, 2.032, 0.000},
                                             {0.000, 128.0, 128.0},
                                             {0.000, 0.000, 0.000}};
static cspace_constants rgb2ycc_constants = {{0.299, 0.587, 0.114},
                                             {-0.169, -0.331, 0.500},
                                             {0.500, -0.419, -0.081},
                                             {0.000, 0.000, 0.000},
                                             {0.000, 128.0, 128.0}};
static cspace_constants rgb2yuv_constants = {{0.299, 0.587, 0.114},
                                             {-0.147, -0.289, 0.436},
                                             {0.615, -0.515, -0.100},
                                             {0.000, 0.000, 0.000},
                                             {0.000, 128.0, 128.0}};

////////////
// Scalar //
////////////

// Apply color space conversion on an input image
void cspace_conversion(uint8_t *src, uint8_t *dst, uint32_t w, uint32_t h, enum cspace_conversion conversion);

// Common non-accelerated conversion using full set of constants
void common_cspace_conversion(uint8_t *src, uint8_t *dst, uint32_t w, uint32_t h, cspace_constants constants);
// Convert image from YUV444 to RGB888 color space
void yuv_to_rgb(uint8_t *src, uint8_t *dst, uint32_t w, uint32_t h, cspace_constants constants);
// Convert image from RGB888 to Gray color space
void rgb_to_gray(uint8_t *src, uint8_t *dst, uint32_t w, uint32_t h);
// Extract specific channel from input image
void channel_extraction(uint8_t *src, uint8_t *dst, uint32_t w, uint32_t h, uint32_t c, uint32_t channel);

/////////
// RVV //
/////////

// Apply color space conversion on an input image
void cspace_conversion_rvv(uint8_t *src, uint8_t *dst, uint32_t w, uint32_t h, enum cspace_conversion conversion);

// Common non-accelerated conversion using full set of constants
void common_cspace_conversion_rvv(uint8_t *src, uint8_t *dst, uint32_t w, uint32_t h, cspace_constants constants);
// Convert image from YUV444 to RGB888 color space
void yuv_to_rgb_rvv(uint8_t *src, uint8_t *dst, uint32_t w, uint32_t h, cspace_constants constants);
// Convert image from RGB888 to Gray color space
void rgb_to_gray_rvv(uint8_t *src, uint8_t *dst, uint32_t w, uint32_t h);
// Extract specific channel from input image
void channel_extraction_rvv(uint8_t *src, uint8_t *dst, uint32_t w, uint32_t h, uint32_t c, uint32_t channel);
