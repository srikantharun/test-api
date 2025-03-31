#include "secure_ip_hal.h"

#if __cplusplus
extern "C" {
#endif

// Tests that can be stimulated from Host, on final 'release' ROMcode:
int test_kse3_csr_rst();
int test_kse3_csr_access();
int test_kse3_ram_access();

// Tests that need extra validation commands, only available in the 'integration' ROMcode:
int test_kse3_cpu();
int test_kse3_otp_read();
int test_kse3_otp_write();
int test_kse3_aor_0_7();
int test_kse3_aor_8_15();
int test_kse3_irom();
int test_kse3_dram_begin();
int test_kse3_dram_middle();
int test_kse3_dram_end();
int test_kse3_iram_begin();
int test_kse3_iram_middle();
int test_kse3_iram_end();
int test_kse3_iram_exec();
int test_kse3_ens();

// Tests that need to be run within our stand - alone testbench, or be adaptated to customer testbench
extern int gIncludeKeyProt;
int test_kse3_irq();
int test_kse3_config();
int test_kse3_aor_tb();
int test_kse3_keybus();
int test_kse3_keyprot();
int test_kse3_keyprot_ip();

#if __cplusplus
}
#endif

/* End of file */
