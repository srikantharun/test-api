// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Max Wipfli <max.wipfli@axelera.ai>
#include <printf.h>
#include <testutils.h>
#include <decoder/decoder.h>
#include "pctl_utils.h"

int main() {
    testcase_init();

    pctl_enable_module(DECODER_MODULE);

    printf("*** test_decoder_reg_info\r\n");

    // No MCU firmware load required as we are only reading registers whose
    // values should be specified in the RTL.

    uint32_t ip_identification_number = DECODER_REG_TOP->ip_identification_number;
    uint32_t ip_architecture = DECODER_REG_TOP->ip_architecture;
    uint32_t ip_date = DECODER_REG_TOP->ip_date;
    uint32_t ip_version = DECODER_REG_TOP->ip_version;

    printf(">> DecIdentificationNumber: 0x%08x\r\n", ip_identification_number);
    printf(">> DecArchitecture:         0x%08x\r\n", ip_architecture);
    printf(">> DecDate:                 0x%08x\r\n", ip_date);
    printf(">> DecVersion:              0x%08x\r\n", ip_version);

    // Check these do not change. Note that this is not "ground truth", but has
    // been obtained when running this test the first time. They are expected to
    // change with new RTL drops.
    CHECK_EQUAL_HEX(ip_identification_number, 0x30ab6e51);
    CHECK_EQUAL_HEX(ip_architecture, 0xb1000801);
    CHECK_EQUAL_HEX(ip_date, 0x20241106);
    CHECK_EQUAL_HEX(ip_version, 0xc43329eb);

    // Check for idempotent reads.
    for (size_t i = 0; i < 16; i++) {
        CHECK_EQUAL_INT(ip_identification_number, DECODER_REG_TOP->ip_identification_number);
        CHECK_EQUAL_INT(ip_architecture, DECODER_REG_TOP->ip_architecture);
        CHECK_EQUAL_INT(ip_date, DECODER_REG_TOP->ip_date);
        CHECK_EQUAL_INT(ip_version, DECODER_REG_TOP->ip_version);
    }
    
    return testcase_finalize();
}
