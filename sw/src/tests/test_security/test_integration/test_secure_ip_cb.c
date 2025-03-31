#include "include/test_secure_ip_cb.h"
#include "include/secure_ip.h"

/**
Seeding the cryptobox before first test

*/
int test_kse3_cb_seed()
{
    int status = execute(KSE3_CMD_CB_TEST_SEED, 0);
    if (status != KSE3_SUCCESS) {
        switch (status) {
        case 0xFE:
            printf("\nERROR: CB SEED reports a bus error (HRESP)");
            break;
        default:
            printf("\nERROR: CB SEED test returned unexpected status 0x%02X", status);
        }
        return 1;
    }
    return 0;
}

/**
Perform a aes self test command

*/
int test_kse3_cb_aes()
{
    int status = execute(KSE3_CMD_CB_TEST_AES, 0);
    if (status != KSE3_SUCCESS) {
        switch (status) {
        case 0xFE:
            printf("\nERROR: CB AES reports a bus error (HRESP)");
            break;
        default:
            printf("\nERROR: CB AES test returned unexpected status 0x%02X", status);
        }
        return 1;
    }
    return 0;
}


/**
Perform a modarith self test command

*/
int test_kse3_cb_modarith()
{
    int status = execute(KSE3_CMD_CB_TEST_MODARITH, 0);
    if (status != KSE3_SUCCESS) {
        switch (status) {
        case 0xFE:
            printf("\nERROR: CB modarith reports a bus error (HRESP)");
            break;
        default:
            printf("\nERROR: CB modarith test returned unexpected status 0x%02X", status);
        }
        return 1;
    }
    return 0;
}


/**
Perform a SHA2 self test command

*/
int test_kse3_cb_sha2()
{
    int status = execute(KSE3_CMD_CB_TEST_SHA2, 0);
    if (status != KSE3_SUCCESS) {
        switch (status) {
        case 0xFE:
            printf("\nERROR: CB sha2 reports a bus error (HRESP)");
            break;
        default:
            printf("\nERROR: CB sha2 test returned unexpected status 0x%02X", status);
        }
        return 1;
    }
    return 0;
}


/**
Perform a sponge basic self test command

*/
int test_kse3_cb_sponge_basic()
{
    int status = execute(KSE3_CMD_CB_TEST_SPONGE_BASIC, 0);
    if (status != KSE3_SUCCESS) {
        switch (status) {
        case 0xFE:
            printf("\nERROR: CB Sponge basic reports a bus error (HRESP)");
            break;
        default:
            printf("\nERROR: CB Sponge basic test returned unexpected status 0x%02X", status);
        }
        return 1;
    }
    return 0;
}


/**
Perform a sponge aead self test command

*/
int test_kse3_cb_sponge_aead()
{
    int status = execute(KSE3_CMD_CB_TEST_SPONGE_AEAD, 0);
    if (status != KSE3_SUCCESS) {
        switch (status) {
        case 0xFE:
            printf("\nERROR: CB Sponge AEAD reports a bus error (HRESP)");
            break;
        default:
            printf("\nERROR: CB Sponge AEAD test returned unexpected status 0x%02X", status);
        }
        return 1;
    }
    return 0;
}/**
Perform a SHA3 self test command

*/
int test_kse3_cb_sha3()
{
	int status = execute(KSE3_CMD_CB_TEST_SHA3, 0);
	if (status != KSE3_SUCCESS) {
		switch (status) {
		case 0xFE:
			printf("\nERROR: CB sha3 reports a bus error (HRESP)");
			break;
		default:
			printf("\nERROR: CB sha3 test returned unexpected status 0x%02X", status);
		}
		return 1;
	}
	return 0;
}
