/**************************************************************************************
HW Interfaces tests

This file contains tests that check the KSE3 interfaces. There are 3 categories of
HW tests:

A) Tests that can be stimulated from Host, on final 'release' ROMcode:
    test_kse3_csr_rst    : Default CSR values after reset.
    test_kse3_csr_access : Host can read/write all CSR registers, in 8 and 32-bits.
    test_kse3_ram_access : Host can read/write public RAM (4.5kB) in 8 and 32-bits.

B) Tests that need extra validation commands, only available in the 'integration' ROMcode:
    test_kse3_otp_write  : KSE3 can write/read correctly all OTP addresses.
    test_kse3_otp_read   : KSE3 can read all OTP addresses without bus error.
    test_kse3_aor        : KSE3 can read/write all AOR registers.
    test_kse3_irom       : KSE3 ROMcode works at various address, including near end of ROM.
    test_kse3_dram       : KSE3 can read/write all RAM (including private), in 8 and 32-bits.
    test_kse3_cpu        : KSE3 internal behaves correctly

C) Tests that need to be run within our stand-alone testbench, or be adaptated to customer testbench:
    test_kse3_config     : Host can retrieve and check config (8-bits).
    test_kse3_irq        : Interrupt can be triggered when properly configured.
    *test_kse3_aor_tb    : Host can check OTP content through testbench (using AOR registers model).
    *test_kse3_scan_mode : Check that 'scan_mode_i' interface has effect on KSE3

    * <-- denotes tests that are not yet implemented

All the above tests will return the number of error that did occur during their execution.

**************************************************************************************/

#include "include/test_secure_ip_hw.h"
#include "include/secure_ip.h"

/**
Test internal CPU

The host forces a reset of the KSE3, then check that all registers report their
advertized default values at reset.

@return error code (0 in case of success)
*/
int test_kse3_cpu()
{
	int status;
	
	// Test CPU's CSR registers at boot
	status = execute(KSE3_CMD_HW_TEST_CPU, 1);
    if (status != KSE3_SUCCESS) {
		printf("\nERROR test_kse3_cpu: CSR registers at reset returned unexpected status 0x%02X", status);
        return status;
    }

	// Test TRAP and privilege mechanism
	status = execute(KSE3_CMD_HW_TEST_CPU, 2);
	if (status != KSE3_SUCCESS) {
		printf("\nERROR test_kse3_cpu: Trap tests returned unexpected status 0x%02X", status);
		return status;
	}

    return 0;
}


/**
Test CSR values on reset

After the host has forced a reset of the KSE3, this test checks that all registers report their
advertized default values at reset, on host-side.

@return number of error(0 in case of success)
*/
int test_kse3_csr_rst()
{
    uint32_t csr_dut;
    uint32_t ahb_addr;
    int error_count = 0;

    /* Reset values, for each CSR register, as described in document */
    const uint32_t csr_refs[] = {
        0x00000000,    /*  0: CMD_CTRL */
        0x00000000,    /*  1: CMD_STATUS */
        0xFFFFFF00,    /*  2: CMD_TRK */
        0x00000000,    /*  3: CMD_PERF (not tested) */
        0x00000000,    /*  4: INT_CTRL */
        0x00000001,    /*  5: PWR_CTRL */

        /* Theses CSR registers are intentionally not checked at reset */
		0x4b534950,    /*  6: HW_ID (ignored because this depends upon customer, project and delivery) */
        0x00000980,    /*  7: NAGRA_ID (ignored because contains an internal version number which is subject to change) */
        0x00000000,    /*  8: DBG_INFO_0 (ignored because it can contain information at reset) */
        0x00000000,    /*  9: DBG_INFO_1 (ignored because it can contain information at reset) */
        0x00000000     /* 10: DBG_INFO_2 (ignored because it can contain information at reset) */
    };
    const int nb_csr_reg = sizeof(csr_refs) / sizeof(uint32_t);

    /* Check each CSR described in 'csr_refs' array above */
    for ( int i=0; i<nb_csr_reg; i++ ) {
        ahb_addr = ADDR_CMD_CTRL + i * sizeof(uint32_t);
        csr_dut = read_reg32(ahb_addr);
		// Skip CMD_PERF and all registeres from HW_ID, which holds startup duration
		if ( ( i < 6 ) && (i != 3 ) ) {
			if (csr_dut != csr_refs[i]) {
				printf("\nERROR: CSR[%0d] at 0x%x holds 0x%08x at reset instead of 0x%08x", i, ahb_addr, csr_dut, csr_refs[i]);
				error_count++;
			}
		}
    }

    return error_count;
}

/**
Perform access test on CSR registers

This tests verifies that:
- Host can write all writeable CSR register, both in 8-bits and 32-bits (all bits toggled).
- Host can read all CSR registers, both in 8-bits and 32-bits accesses.

@return number of error(0 in case of success)
*/
int test_kse3_csr_access()
{
    uint32_t ahb_addr;
    uint32_t dut_dout32;
    uint8_t dut_dout8;
    uint32_t ref_dout32;
    uint8_t ref_dout8;
    uint32_t data32;
    uint8_t data8;
    int skip_register;
    int error_count = 0;

    /* Write/Read sequence for each CSR register we can test (RO registers skipped, they would raise HRESP)
       The columns Write0 and Write1 corresponds to 2 successive writes that gives optimium write coverage.
       The column Write2 is here to put back the registers in a reset-state when leaving the test.
       The columns Readback0 and Readback1 reflects the expected content of each register after the corresponding write.*/
    const uint32_t sequence[][6] = {
        /* AHB address,    Write0    Readback0     Write1      Readback1   Write2 */
        { ADDR_CMD_CTRL,   0xE1C3785A, 0xE1C3781A, 0x1E3C87A4, 0x1E3C8724, 0x00000000 }, /* bit 0 not set as it would start IP processing */
        /* ADDR_CMD_STATUS skipped because it is read-only */
        { ADDR_CMD_TRK,    0xAE1C3785, 0xAE1C3785, 0x51E3C87A, 0x51E3C87A, 0xFFFFFF00 },
        /* ADDR_CMD_PERF skipped because it is read-only */
        { ADDR_INT_CTRL,   0x5AE1C378, 0x00000000, 0xA51E3C87, 0x00000000, 0x00000000 },
        { ADDR_PWR_CTRL,   0x85AE1C37, 0x00000001, 0x7A51E3C9, 0x00000001, 0x00000001 }, /* bit 0 not clear as it would put the IP to sleep */
        /* ADDR_HW_ID and ADDR_NAGRA_ID skipped because they are read-only */
        { ADDR_DBG_INFO_0, 0x785AE1C3, 0x785AE1C3, 0x87A51E3C, 0x87A51E3C, 0x00000000 },
        { ADDR_DBG_INFO_1, 0x3785AE1C, 0x3785AE1C, 0xC87A51E3, 0xC87A51E3, 0x00000000 },
        { ADDR_DBG_INFO_2, 0xC3785AE1, 0xC3785AE1, 0x3C87A51E, 0x3C87A51E, 0x00000000 },
    };
    const int nb_tests = sizeof(sequence) / sizeof(sequence[0]);

    /* To ensure all bits can toogle, we do 2 passes (named 0 and 1) */
    for (int pass = 0; pass <= 1; pass++) {

        /* Perform all Write0/1 in 32-bits */
        for (int i = 0; i < nb_tests; i++) {
            ahb_addr = sequence[i][0];
            data32 = sequence[i][pass * 2 + 1];     /* Write0 or Write1 */
            write_reg32(ahb_addr, data32);
        }

        /* Perform all Readback0/1 in 32-bits*/
        for (int i = 0; i < nb_tests; i++) {
            ahb_addr = sequence[i][0];
            ref_dout32 = sequence[i][pass*2 + 2];
            dut_dout32 = read_reg32(ahb_addr);  /* Readback0 or Readback1 */
            if (dut_dout32 != ref_dout32) {
                printf("\nERROR: CSR at 0x%x holds 0x%08x after readback_%0d, instead of 0x%08x", ahb_addr, dut_dout32, pass, ref_dout32);
                error_count++;
            }
        }
    }

    /* Perform all Write0 in 8-bits, from LSB to MSB and verify with readbacks0 in 32-bits */
    for (unsigned byte = 0; byte < sizeof(uint32_t); byte++) {

        /* Write a single byte to each CSR writable registers */
        for (int i = 0; i < nb_tests; i++) {
            ahb_addr = sequence[i][0] + byte;
            data8 = (sequence[i][1] >> (byte*8)) & 0xFF;     /* Write0 */
            write_bytes(ahb_addr, &data8, 1);
        }

        /* Verify the value using a 32-bit read */
        for (int i = 0; i < nb_tests; i++) {
            ahb_addr = sequence[i][0];
            ref_dout32 = ( sequence[i][4] & (0xFFFFFF00<<(byte*8))) | ( sequence[i][2] & ~(0xFFFFFF00 << (byte * 8)));
            dut_dout32 = read_reg32(ahb_addr);  /* Readback0 or Readback1 */
            if (dut_dout32 != ref_dout32) {
                printf("\nERROR: CSR at 0x%x holds 0x%08x write0 of byte %0d, instead of 0x%08x", ahb_addr, dut_dout32, byte, ref_dout32);
                error_count++;
            }
        }
    }

    /* Perform Write1 in 32-bits */
    for (int i = 0; i < nb_tests; i++) {
        ahb_addr = sequence[i][0];
        data32 = sequence[i][3];     /* Write1 */
        write_reg32(ahb_addr, data32);
    }

    /* Readback1 in 8-bits */
    for (unsigned byte = 0; byte < sizeof(uint32_t); byte++) {
        for (int i = 0; i < nb_tests; i++) {
            ahb_addr = sequence[i][0] + byte;
            ref_dout8 = (sequence[i][4] >> (byte * 8)) & 0xFF;     /* Readback1 */
            read_bytes(ahb_addr, &dut_dout8, 1);
            if (dut_dout8 != ref_dout8) {
                printf("\nERROR: CSR at 0x%x holds 0x%02x write0 of byte %0d, instead of 0x%02x", ahb_addr, dut_dout8, byte, ref_dout8);
                error_count++;
            }
        }
    }

    /* Put CSR registers back to initial default values */
    for (int i = 0; i < nb_tests; i++) {
        ahb_addr = sequence[i][0];
        data32 = sequence[i][5];     /* Write2 */
        write_reg32(ahb_addr, data32);
    }

    /* For all registers that are read-only, check we can read them in 32-bits and 8-bits */
    for (ahb_addr = ADDR_CMD_CTRL; ahb_addr <= ADDR_DBG_INFO_2; ahb_addr += sizeof(uint32_t)) { //spike simulation does not allow accessing 32 bits only so it will receive a slave error when trying to read this address with 64 bits

        /* Skip registeres that we have already tested above */
        skip_register = 0;
        for (int i = 0; i < nb_tests; i++) {
            if (ahb_addr == sequence[i][0]) {
                skip_register = 1;
                break;
            }
        }
        if (skip_register) {
            break;
        }

        /* Read the register in 32-bits */
        ref_dout32 = read_reg32(ahb_addr);

        /* Then read it with 8-bits (this code assumes little-endian host CPU) */
        read_bytes(ahb_addr+2, &dut_dout8, 1);
        dut_dout32 = dut_dout8 << 16;
        read_bytes(ahb_addr+1, &dut_dout8, 1);
        dut_dout32 |= dut_dout8 << 8;
        read_bytes(ahb_addr+3, &dut_dout8, 1);
        dut_dout32 |= dut_dout8 << 24;
        read_bytes(ahb_addr+0, &dut_dout8, 1);
        dut_dout32 |= dut_dout8;
        if (dut_dout32 != ref_dout32) {
            printf("\nERROR: read-only CSR at 0x%x byte-read 0x%08x instead of word-read 0x%08x", ahb_addr, dut_dout32, ref_dout32);
            error_count++;
        }
    }

    return error_count;
}

/**
Perform a public RAM selftest

This test attempts read/write whole part of the RAM that is accessible from the host.

It contains a mix of:
- 8-bits, and 32-bits accesses,
- read and writes,
- ascending and descending addressing

@return number of error(0 in case of success)
*/
int test_kse3_ram_access()
{
    uint32_t ahb_addr;
    uint8_t ref8[4];
    uint32_t ref32;
    uint8_t dut_dout8;
    uint32_t dut_dout32;
    int error_count = 0;

    /* Write all accessible RAM using ascending bytes-accesses */
    for (ahb_addr = ADDR_BASE_RAM; ahb_addr < ADDR_BASE_RAM+ SHARED_RAM_SIZE; ahb_addr +=(sizeof(uint32_t)*32) ) {

        /* Prepare a pattern containing LSB(address) */
        for (unsigned byte = 0; byte < sizeof(uint32_t); byte++) {
            ref8[byte] = ahb_addr & 0xFF;
        }

        /* Write bytes in a non-linear way */
        write_bytes(ahb_addr + 1, ref8 + 1, 1);
        write_bytes(ahb_addr + 3, ref8 + 3, 1);
        write_bytes(ahb_addr + 0, ref8 + 0, 1);
        write_bytes(ahb_addr + 2, ref8 + 2, 1);
    }

    /* Readback all accessible RAM using descending 32-bits accesses */
    for (ahb_addr = ADDR_BASE_RAM + SHARED_RAM_SIZE; ahb_addr > ADDR_BASE_RAM; ) {
        ahb_addr -= (sizeof(uint32_t)*32);

        /* Re-compute reference pattern */
        for (unsigned byte = 0; byte < sizeof(uint32_t); byte++) {
            ref8[byte] = ahb_addr & 0xFF;
        }
        ref32 = (ref8[3] << 24) | (ref8[2] << 16) | (ref8[1] << 8) | ref8[0];

        /* Readback and check 32-bits */
        dut_dout32 = read_reg32(ahb_addr);  /* Readback0 or Readback1 */
        if (dut_dout32 != ref32) {
            printf("\nERROR: RAM at 0x%x 32-bits readback 0x%08x instead of 0x%08x", ahb_addr, dut_dout32, ref32);
            error_count++;
        }
    }

    /* Write all accessible RAM using ascending 32-bits accesses. Pattern is 32-bits based */
    for (ahb_addr = ADDR_BASE_RAM; ahb_addr < ADDR_BASE_RAM + SHARED_RAM_SIZE;  ahb_addr += (sizeof(uint32_t)*32) ) {
        ref32 = (ahb_addr << 16) | (~ahb_addr & 0xFFFF);
        write_reg32(ahb_addr, ref32);
    }

    /* Readback all accessible RAM using descending 8-bits accesses */
    for (ahb_addr = ADDR_BASE_RAM+ SHARED_RAM_SIZE; ahb_addr > ADDR_BASE_RAM; ) {
        ahb_addr -= (sizeof(uint32_t)*32);

        /* Compute reference pattern */
        ref32 = (ahb_addr << 16) | (~ahb_addr & 0xFFFF);
        for (unsigned byte = sizeof(uint32_t); byte--;) {
            ref8[byte] = (uint8_t)(ref32 >> (byte * 8));

            /* Read and check byte */
            read_bytes(ahb_addr+byte, &dut_dout8, 1);
            if (dut_dout8 != ref8[byte]) {
                printf("\nERROR: RAM at 0x%x byte readback 0x%02x instead of 0x%02x", ahb_addr + byte, dut_dout8, ref8[byte]);
                error_count++;
            }
        }
    }

    return error_count;
}


/**
Perform a OTP HW self test command

During this test, the KSE3 will attempt to write all OTP with unique bytes.
It will then read-back and report error throught the CMD_STATUS CSR register:

0xE5) Success

0xFE) A bus error has been detected (HRESP=1)

0xFF) An OTP byte has been readback incorrectly. Extra information:
    - DBG_INFO_0 = byte-offset in OTP where the mismatch occured (can't be readback from host)
    - DBG_INFO_1 = value read-back from OTP (can't be readback from host)

WARNING: because this test **writes** the OTP, applicative commands using the OTP
         will fail, after this test (typ. GenSeed/LoadSeed).
*/
int test_kse3_otp_write()
{
    int status = execute(KSE3_CMD_HW_TEST_OTP_WRITE,0);
    if (status != KSE3_SUCCESS) {
        switch (status) {
        case 0xFF: {
            printf("\nERROR: OTP HW write reports failure");
            break;
        }
        case 0xFE:
            printf("\nERROR: OTP HW write reports a bus error (HRESP=1)");
            break;
        default:
            printf("\nERROR: OTP HW write test returned unexpected status 0x%02X", status);
        }
        return 1;
    }
    return 0;
}

/**
Perform a OTP HW self test command

During this test, the KSE3 will attempt to read all OTP, byte-after-byte.
This test does not assume a particular content, but just checks that reading
the OTP does not trigger a bus error.

0xE5) Success

0xFE) A bus error has been detected (HRESP=1)
*/
int test_kse3_otp_read()
{
    int status = execute(KSE3_CMD_HW_TEST_OTP_READ,0);
    if (status != KSE3_SUCCESS) {
        switch (status) {
        case 0xFE:
            printf("\nERROR: OTP HW read reports a bus error (HRESP)");
            break;
        default:
            printf("\nERROR: OTP HW read test returned unexpected status 0x%02X", status);
        }
        return 1;
    }
    return 0;
}


/**
Perform a test to access AOR registers. 8 registers 8-bits on APB bus
This test will flip each bits of each registers, this is an internal test

@return number of error (0 in case of success)
*/
int test_kse3_aor_0_7()
{
    int status;
    uint8_t operation = 0; // read reg
    uint8_t value = 0xAA;
    uint16_t sub_cmd = 0;

    /* Reset values, for each AOR register, as described in document */
    const uint32_t aor_refs[] = {
        0x00,    /*  0: REG1 */
        0xFF,    /*  1: REG2 */
        0x00,    /*  2: REG3 */
        0xFF,    /*  3: REG4 */
        0x00,    /*  4: REG5 */
        0xFF,    /*  5: REG6 */
        0x00,    /*  6: REG7 */
        0x00,    /*  7: REG8 */
    };

    // check init value
    for (uint8_t i = 0; i < 8; i++) {
        sub_cmd = (operation << 4) | ((i & 0x7) << 5) | (aor_refs[i] << 8);
        status = execute(KSE3_CMD_HW_TEST_AOR_0_7, sub_cmd);
        if (status != KSE3_SUCCESS) {
            printf("\nERROR test_AOR_rw (reset value reg : %d ): KSE3_CMD_HW_TEST returned unexpected status 0x%02X",i, status);
            return status; /* in case of failure, status contains the number of read errors  */
        }
    }

    operation = 1; // write reg
    for (uint8_t i = 0; i < 8; i++) {

        sub_cmd = (operation << 4) | ((i & 0x7) << 5) | (value << 8);

        status = execute(KSE3_CMD_HW_TEST_AOR_0_7, sub_cmd);
        if (status != KSE3_SUCCESS) {
            printf("\nERROR test_AOR_rw (write reg : %d) : KSE3_CMD_HW_TEST returned unexpected status 0x%02X", i, status);
            return status; /* in case of failure, status contains the number of read errors  */
        }

        value ^= 0xFF;

    }

    operation = 0; // read reg
    for (uint8_t i = 0; i < 8; i++) {
        if (i >= 6) {
            value = 0;
        }

        sub_cmd = (operation << 4) | ((i & 0x7) << 5) | (value << 8);

        status = execute(KSE3_CMD_HW_TEST_AOR_0_7, sub_cmd);
        if (status != KSE3_SUCCESS) {
            printf("\nERROR test_AOR_rw (read reg : %d) : KSE3_CMD_HW_TEST returned unexpected status 0x%02X", i, status);
            return status; /* in case of failure, status contains the number of read errors  */
        }

        value ^= 0xFF;

    }

    return 0;
}


/**
Perform a test to access AOR registers. 8 registers 8-bits on APB bus
This cmd can read or write each register

@return number of error (0 in case of success)
*/
int test_kse3_aor_8_15()
{
    int status;
    uint8_t operation = 0; // write reg
    uint8_t value = 0xAA;
    uint16_t sub_cmd = 0;


    /* Reset values, for each aor register, as described in document */
    const uint32_t aor_refs[] = {
        0x00,    /*  0: REG1 */
        0x00,    /*  1: REG2 */
        0x00,    /*  2: REG3 */
        0x00,    /*  3: REG4 */
        0x00,    /*  4: REG5 */
        0x00,    /*  5: REG6 */
        0x00,    /*  6: REG7 */
        0x00,    /*  7: REG8 */
    };

    // check init value
    for (uint8_t i = 0; i < 8; i++) {
        sub_cmd = (operation << 4) | ((i & 0x7) << 5) | (aor_refs[i] << 8);
        status = execute(KSE3_CMD_HW_TEST_AOR_8_15, sub_cmd);
        if (status != KSE3_SUCCESS) {
            printf("\nERROR test_AOR_rw : KSE3_CMD_HW_TEST returned unexpected status 0x%02X", status);
            return status; /* in case of failure, status contains the number of read errors  */
        }
    }


    operation = 1; // write reg
    for (uint8_t i = 0; i < 8; i++) {

        sub_cmd = (operation << 4) | ((i & 0x7) << 5) | (value << 8);

        status = execute(KSE3_CMD_HW_TEST_AOR_8_15, sub_cmd);
        if (status != KSE3_SUCCESS) {
            printf("\nERROR test_AOR_rw : KSE3_CMD_HW_TEST returned unexpected status 0x%02X", status);
            return status; /* in case of failure, status contains the number of read errors  */
        }

        value ^= 0xFF;

    }

    operation = 0; // read reg
    for (uint8_t i = 0; i < 8; i++) {

        sub_cmd = (operation << 4) | ((i & 0x7) << 5) | (value << 8);

        status = execute(KSE3_CMD_HW_TEST_AOR_8_15, sub_cmd);
        if (status != KSE3_SUCCESS) {
            printf("\nERROR test_AOR_rw : KSE3_CMD_HW_TEST returned unexpected status 0x%02X", status);
            return status; /* in case of failure, status contains the number of read errors  */
        }

        value ^= 0xFF;

    }



    return 0;
}



/**
Perform a test to that KSE3 can execute ROM located near end of the ROM mapping.

This test is intentionnally placed into a section that lies very close to end of ROM.

@return number of error (0 in case of success)
*/
int test_kse3_irom()
{
    int status;
    int error_count = 0;

    /* Execute code near the end of the ROM */
    status = execute(KSE3_CMD_HW_TEST_ROM, 0);
    if (status != 0x47) {
        printf("\nERROR: test_kse3_rom() cannot check proof of execution (STATUS 0x%02x)", status);
        error_count++;
    }

    return error_count;
}


/**
Perform a test to that KSE3 can read and write beginning of D-RAM, including the area not accessible by host.
@return 0 for success
*/
int test_kse3_dram_begin()
{
	uint8_t status = execute(KSE3_CMD_HW_TEST_DRAM, 0);
	return (status == KSE3_SUCCESS) ? 0 : status;
}

/**
Perform a test to that KSE3 can read and write middle of D-RAM.
@return 0 for success
*/
int test_kse3_dram_middle()
{
	uint8_t status = execute(KSE3_CMD_HW_TEST_DRAM, 1);
	return (status == KSE3_SUCCESS) ? 0 : status;
}

/**
Perform a test to that KSE3 can read and write end of D-RAM.
@return 0 for success
*/
int test_kse3_dram_end()
{
	uint8_t status = execute(KSE3_CMD_HW_TEST_DRAM, 2);
	return (status == KSE3_SUCCESS) ? 0 : status;
}

/**
Perform a test to that KSE3 can read and write beginning of I-RAM.
@return 0 for success
*/
int test_kse3_iram_begin()
{
	uint8_t status = execute(KSE3_CMD_HW_TEST_IRAM, 0);
	return (status == KSE3_SUCCESS) ? 0 : status;
}

/**
Perform a test to that KSE3 can read and write middle of I-RAM.
@return 0 for success
*/
int test_kse3_iram_middle()
{
	uint8_t status = execute(KSE3_CMD_HW_TEST_IRAM, 1);
	return (status == KSE3_SUCCESS) ? 0 : status;
}

/**
Perform a test to that KSE3 can read and write end of I-RAM.
@return 0 for success
*/
int test_kse3_iram_end()
{
	uint8_t status = execute(KSE3_CMD_HW_TEST_IRAM, 2);
	return (status == KSE3_SUCCESS) ? 0 : status;
}

/**
Perform a test to that KSE3 can execute code place in I-RAM.
@return 0 for success
*/
int test_kse3_iram_exec()
{
	uint8_t status = execute(KSE3_CMD_HW_TEST_IRAM_EXEC, 0);
	return (status == KSE3_SUCCESS) ? 0 : status;
}   

/**
Perform a test to that KSE3 can read and write whole RAM, including area not accessible by host.

@param[in] area selects the 1.5kB slice to test (0:start, 1:middle, 2:end)

@return number of error (0 in case of success)
*/
int test_kse3_iram(const uint8_t area)
{
	int status;
	int error_count = 0;

	status = execute(KSE3_CMD_HW_TEST_IRAM, area);
	if (status != KSE3_SUCCESS) {
		switch (status) {
		case 0xFA: {
			uint32_t address = read_reg32(ADDR_DBG_INFO_0);
			uint32_t dut = read_reg32(ADDR_DBG_INFO_1);
			uint32_t ref = read_reg32(ADDR_DBG_INFO_2);
			printf("\nERROR: RAM HW test failed at address 0x%x (read 0x%08x intead of 0x%08x)", address, dut, ref);
			error_count = 1;
			break;
		}
		case 0xFB: {
			uint32_t address = read_reg32(ADDR_DBG_INFO_0);
			uint32_t dut = read_reg32(ADDR_DBG_INFO_1);
			uint32_t ref = read_reg32(ADDR_DBG_INFO_2);
			printf("\nERROR: RAM HW test failed at address 0x%x (read 0x%02x intead of 0x%02x)", address, dut, ref);
			error_count = 1;
			break;
		}
		default:
			printf("\nERROR: RAM HW test failed with unknown status 0x%x", status);
			error_count = 1;
		}
	}

	return error_count;
}

/**
Perform a test to that KSE3 can read the hardware config_i primary input.

LIMITATION: This test requires Nagra stand-alone testbench (or adaptation for customer testbench).

TODO: rework this test as the 'config' primary input is now driving memories sizes.
      This test was initially developped to test 'soc_config', which had no direct hardware effect.
	  Changing the memories size in live is NOT supported.

@return number of error (0 in case of success)
*/
int test_kse3_config()
{
    int status;
    int error_count = 0;

    /* Set of config values to tests */
    uint8_t ref_config[] = { 0x00, 0x5A, 0x29, 0xA5, 0xFF };
    const int nb_config = sizeof(ref_config);

    /* Memorize the current Config that is currently set in the testbench */
    uint8_t original_config = read_reg32(TB_REGS_CONFIG) & 0xFF;

    /* Test a set of different values for config field */
    for (int i = 0; i<nb_config; i++) {

        /* Inject the config value into the testbench */
        write_reg32(TB_REGS_CONFIG, ref_config[i]);

        /* Ask the KSE3 to read it from inside */
        status = execute(KSE3_CMD_HW_TEST_CONFIG, ref_config[i]<<4);
        if (status != KSE3_SUCCESS) {
            printf("\nERROR: SoC config HW test failed with unknown status 0x%x", status);
            error_count++;
            break;
        }
    }

    /* Restore the original config value into the testbench */
    write_reg32(TB_REGS_CONFIG, original_config);

    return error_count;
}


/**
Check of the IRQ output signal

LIMITATION: This test requires Nagra stand-alone testbench (or adaptation for customer testbench).

@return number of error (0 in case of success)
*/
int test_kse3_irq()
{
    int status;
    int error_count = 0;
    uint32_t ctrl;
    uint32_t int_ctrl;

    /* Clear the IRQ signal (may have been set by previous command) */
    write_reg32(ADDR_INT_CTRL, 0x00000001);

    /* Verify the IRQ signal flag and signal are clear */
    int_ctrl = read_reg32(ADDR_INT_CTRL);
    if ( (int_ctrl & 0x1) != 0 ) {
        printf("\nERROR: IRQ flag in INT_CTRL(0) is not clear (INT_CTRL=0x%08x)", int_ctrl);
        error_count++;
    }

    /* Run a command in the KSE3 (do it manually, not using execute(), because it auto-clears IRQ) */
    write_reg32(ADDR_CMD_CTRL, (uint32_t)KSE3_CMD_CB_TEST_SEED << 24 | 1);
    do {
        ctrl = read_reg32(ADDR_CMD_CTRL);
    } while (ctrl & 1);
    status = read_reg32(ADDR_CMD_STATUS) & 0xFF;
    if (status != KSE3_SUCCESS) {
        printf("\nERROR: INIT_ROT command failed during RAM test (status 0x%x)", status);
        error_count++;
    }

    int_ctrl = read_reg32(ADDR_INT_CTRL);
    if ( (int_ctrl & 0x1) != 0x1) {
        printf("\nERROR: IRQ flag in INT_CTRL(0) is not set (INT_CTRL=0x%08x)", int_ctrl);
        error_count++;
    }

    /* Clear the IRQ signal */
    write_reg32(ADDR_INT_CTRL, 0x00000000 ); /* Check the written value has no effect */

    /* Verify the IRQ signal flag and signal are clear */
    int_ctrl = read_reg32(ADDR_INT_CTRL);
    if ( (int_ctrl & 0x1) != 0) {
        printf("\nERROR: IRQ flag in INT_CTRL(0) cannot be cleared (INT_CTRL=0x%08x)", int_ctrl);
        error_count++;
    }

    return error_count;
}


/**
Perform a test to access AOR registers. 8 registers 8-bits on ahb bus from testbench
This test will flip each bits of each registers

@return number of error (0 in case of success)
*/
int test_kse3_aor_tb()
{
    int ref_val = 0x11223344;
    int read_val = 0;
    uint8_t read_val_bytes = 0;
    int err_count = 0;
    uint16_t sub_cmd;
    int status;
    uint8_t operation = 0; // read register
    uint8_t cmd;


    for (uint8_t i = 0; i < 4; i++) {

        write_reg32(TB_AHB_AOR_ADDR + (4*i), ref_val);
        ref_val ^= (0xFF << i);

    }

    ref_val = 0x11223344;
    for (uint8_t i = 0; i < 4; i++) {

        read_val = read_reg32(TB_AHB_AOR_ADDR + (4*i));
        if (read_val != ref_val) {
            printf("\nERROR test_unlock_regs_tb : read value at offset 0x 0x%x don't match expected value (0x%02x != 0x%02x)\n", 4 * i, read_val, ref_val);
            err_count++;
        }

        for (uint8_t j = 0; j < 4; j++) {

            if (i < 2) {
                cmd = KSE3_CMD_HW_TEST_AOR_0_7;
            }
            else {
                cmd = KSE3_CMD_HW_TEST_AOR_8_15;
            }

            sub_cmd = (operation << 4) | (((j+(i*4)) & 0x7) << 5) | (  ((ref_val >> (8*j) ) & 0xff )<< 8);
            status = execute(cmd, sub_cmd);
            if (status != KSE3_SUCCESS) {
                printf("\nERROR test_unlock_regs_rw (read reg : %d) : KSE3_CMD_HW_TEST returned unexpected status 0x%02X",j + i*4, status);
                return status; /* in case of failure, status contains the number of read errors  */
            }
        }

        ref_val ^= (0xFF << i);
    }

    // test 8bits access
    uint8_t ref_val_bytes = 0xAA;
    for (uint8_t i = 0; i < 16; i++) {
        write_bytes((TB_AHB_AOR_ADDR + i), &ref_val_bytes, 1);
        ref_val_bytes ^= 0xff;
    }

    ref_val_bytes = 0xAA;
    for (uint8_t i = 0; i < 16; i++) {
        read_bytes((TB_AHB_AOR_ADDR +  i), &read_val_bytes, 1);
        if (read_val_bytes != ref_val_bytes) {
            printf("\nERROR test_unlock_regs_tb : read value in bytes don't match expected value (0x%02x != 0x%02x)\n", read_val_bytes, ref_val_bytes);
            err_count++;
        }
        ref_val_bytes ^= 0xff;
    }

    // fill registers with reset value
    const uint32_t aor_refs[] = {
        0xff00ff00,    /*  0: REG1 */
        0x0000ff00,    /*  1: REG2 */
        0x00000000,    /*  2: REG3 */
        0x00000000,    /*  3: REG4 */
    };

    for (uint8_t i = 0; i < 4; i++) {
        write_reg32(TB_AHB_AOR_ADDR + (4 * i), aor_refs[i]);
    }


    return err_count;
}


/**
Perform a test to access KeyBus registers

@return number of error (0 in case of success)
*/
int test_kse3_keybus()
{
    uint32_t data32;
    uint32_t ref32;
    uint32_t ahb_addr;
    int error_count = 0;
    int status;
    
    // TODO: move these constants to vhd package or .h file?
    const uint32_t NB_SEL = 2;        // number of kb_sel selection bits = number of register banks in tb_keybus
    const uint32_t NB_REG_BANK = 16;  // number of registers in each bank in tb_keybus = (number kb_addr bits)^2
    
    // enable KeyBus testing in the testbench (clear bit kp_ena of dut_ctrl_reg in tb_reg)
    data32 = read_reg32(TB_REGS_CTRL);
    write_reg32(TB_REGS_CTRL, data32 & ~(1 << 24));
    
    // write 0 to all tb_keybus registers
    for (uint32_t i = 0; i < NB_SEL; i++) {  // i indexes the register bank
        for (uint32_t j = 0; j < NB_REG_BANK; j++) {  // j indexes the register inside the bank
            ahb_addr = TB_KEYBUS_BASE_ADDR + (i*NB_REG_BANK + j) * sizeof(uint32_t);
            write_reg32(ahb_addr, 0);
            data32 = read_reg32(ahb_addr);
            if (data32 != 0) {
                printf( "\nERROR: tb_keybus register read at 0x%x: got 0x%08x, expected 0x%08x", ahb_addr, data32, 0 );
                error_count++;
            }
        }
    }
    
    // execute test_keybus function in integration romcode
    status = execute(KSE3_CMD_HW_TEST_KEYBUS, 0);
    if (status != KSE3_SUCCESS) {
        printf("\nERROR: KSE3_CMD_HW_TEST_KEYBUS command failed (status 0x%x)", status);
        error_count++;
    }
    
    // check that tb_keybus registers have been written with expected values
    for (uint32_t i = 0; i < NB_SEL; i++) {  // i indexes the register bank
        for (uint32_t j = 0; j < NB_REG_BANK; j++) {  // j indexes the register inside the bank
            ahb_addr = TB_KEYBUS_BASE_ADDR + (i*NB_REG_BANK + j) * sizeof(uint32_t);
            data32 = read_reg32(ahb_addr);
            ref32 = (j << 28) | (j << 24) | (j << 20) | (j << 16) | (j << 12) | (j << 8) | (j << 4) | (j << 0);
            if (data32 != ref32) {
                printf( "\nERROR: tb_keybus register read at 0x%x: got 0x%08x, expected 0x%08x", ahb_addr, data32, ref32 );
                error_count++;
            }
        }
    }

    return error_count;
}


/**
Perform a test to access the entropy source. This test will generate a seed of 1024 bits and check the health tests

@return number of error (0 in case of success)
*/
int test_kse3_ens()
{
	uint8_t status = execute(KSE3_CMD_HW_TEST_ENS, 0);
	return (status == KSE3_SUCCESS) ? 0 : status;
}



