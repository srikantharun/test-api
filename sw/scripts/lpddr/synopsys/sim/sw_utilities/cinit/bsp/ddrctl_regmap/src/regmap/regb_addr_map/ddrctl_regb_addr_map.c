// ------------------------------------------------------------------------------
//
// Copyright 2023 Synopsys, INC.
//
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
//            Inclusivity and Diversity" (Refer to article 000036315 at
//                        https://solvnetplus.synopsys.com)
//
// ------------------------------------------------------------------------------

#include "ddrctl_regb_addr_map.h"

const ddrctl_field_t reg_addrmap1[] = {
    {"addrmap_cs_bit0",  0,  6, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL             , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_addrmap10[] = {
    {"addrmap_row_b2",  0,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_row_b3",  8,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_row_b4", 16,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_row_b5", 24,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL            , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_addrmap11[] = {
    {"addrmap_row_b0",  0,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_row_b1",  8,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL            , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_addrmap12[] = {
    {"nonbinary_device_density",  0,  3, ACCESS_READ_WRITE, PROG_STATIC},
    {"bank_hash_en"            ,  4,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                      , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_addrmap3[] = {
    {"addrmap_bank_b0",  0,  6, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_bank_b1",  8,  6, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_bank_b2", 16,  6, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL             , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_addrmap4[] = {
    {"addrmap_bg_b0",  0,  6, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_bg_b1",  8,  6, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL           , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_addrmap5[] = {
    {"addrmap_col_b7" ,  0,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_col_b8" ,  8,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_col_b9" , 16,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_col_b10", 24,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL             , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_addrmap6[] = {
    {"addrmap_col_b3",  0,  4, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_col_b4",  8,  4, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_col_b5", 16,  4, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_col_b6", 24,  4, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL            , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_addrmap7[] = {
    {"addrmap_row_b14",  0,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_row_b15",  8,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_row_b16", 16,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_row_b17", 24,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL             , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_addrmap8[] = {
    {"addrmap_row_b10",  0,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_row_b11",  8,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_row_b12", 16,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_row_b13", 24,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL             , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_addrmap9[] = {
    {"addrmap_row_b6",  0,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_row_b7",  8,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_row_b8", 16,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {"addrmap_row_b9", 24,  5, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL            , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

