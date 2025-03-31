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

#include "ddrctl_regb_arb_port.h"

const ddrctl_field_t reg_pccfg[] = {
    {"go2critical_en" ,  0,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"pagematch_limit",  4,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL             , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_pcfgqos0[] = {
    {"rqos_map_level1" ,  0,  4, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"rqos_map_level2" ,  8,  4, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"rqos_map_region0", 16,  2, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"rqos_map_region1", 20,  2, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"rqos_map_region2", 24,  2, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL              , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_pcfgqos1[] = {
    {"rqos_map_timeoutb",  0, 11, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"rqos_map_timeoutr", 16, 11, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL               , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_pcfgr[] = {
    {"rd_port_priority"    ,  0, 10, ACCESS_READ_WRITE, PROG_STATIC},
    {"rd_port_aging_en"    , 12,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"rd_port_urgent_en"   , 13,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"rd_port_pagematch_en", 14,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"rrb_lock_threshold"  , 20,  4, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                  , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_pcfgw[] = {
    {"wr_port_priority"    ,  0, 10, ACCESS_READ_WRITE, PROG_STATIC},
    {"wr_port_aging_en"    , 12,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"wr_port_urgent_en"   , 13,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {"wr_port_pagematch_en", 14,  1, ACCESS_READ_WRITE, PROG_STATIC},
    {NULL                  , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_pcfgwqos0[] = {
    {"wqos_map_level1" ,  0,  4, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"wqos_map_level2" ,  8,  4, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"wqos_map_region0", 16,  2, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"wqos_map_region1", 20,  2, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"wqos_map_region2", 24,  2, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL              , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_pcfgwqos1[] = {
    {"wqos_map_timeout1",  0, 11, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {"wqos_map_timeout2", 16, 11, ACCESS_READ_WRITE, PROG_QUASI_DYNAMIC},
    {NULL               , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_pctrl[] = {
    {"port_en",  0,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL     , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_pstat[] = {
    {"rd_port_busy_0",  0,  1, ACCESS_READ, PROG_DYNAMIC},
    {"wr_port_busy_0", 16,  1, ACCESS_READ, PROG_DYNAMIC},
    {NULL            , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_sbrctl[] = {
    {"scrub_en"             ,  0,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"scrub_during_lowpower",  1,  1, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"scrub_burst_length_nm",  4,  3, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"scrub_interval"       ,  8, 13, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"scrub_cmd_type"       , 24,  2, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {"scrub_burst_length_lp", 28,  3, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL                   , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_sbrrange0[] = {
    {"sbr_address_range_mask_0",  0, 32, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL                      , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_sbrrange1[] = {
    {"sbr_address_range_mask_1",  0,  8, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL                      , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_sbrstart0[] = {
    {"sbr_address_start_mask_0",  0, 32, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL                      , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_sbrstart1[] = {
    {"sbr_address_start_mask_1",  0,  8, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL                      , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_sbrstat[] = {
    {"scrub_busy",  0,  1, ACCESS_READ, PROG_DYNAMIC},
    {"scrub_done",  1,  1, ACCESS_READ, PROG_DYNAMIC},
    {NULL        , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

const ddrctl_field_t reg_sbrwdata0[] = {
    {"scrub_pattern0",  0, 32, ACCESS_READ_WRITE, PROG_DYNAMIC},
    {NULL            , 32, 32, ACCESS_UNKNOWN, PROG_UNKNOWN},
};

