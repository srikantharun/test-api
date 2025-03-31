#pragma once

#include <printf.h>
#include <stdbool.h>
#include <stdint.h>
#include <testutils.h>
#include <memorymap.h>

#include "secure_ip.h"


// Same level as Posix syslog
#define LOG_EMERG   0
#define LOG_ALERT   1
#define LOG_CRIT    2
#define LOG_ERROR   3
#define LOG_WARNING 4
#define LOG_NOTICE  5
#define LOG_INFO    6
#define LOG_DEBUG   7

#if __cplusplus
extern "C" {
#endif

    /* Prototypes */
    int secure_ip_open();
    void secure_ip_close();
    void write_reg32(size_t addr, uint32_t value);
    uint32_t read_reg32(size_t addr);
    void write_bytes(size_t addr, uint8_t* buffer, uint32_t length);
    void read_bytes(size_t addr, uint8_t* buffer, uint32_t length);
    uint8_t execute(uint8_t token, uint16_t sub_cmd);
    void reset();
    void log_open(const char *filename);
    void log_close();

	/* Extra test command, sepcifc to SystemC */
	int test_pipelined_ahb();

#if __cplusplus
}
#endif

/* End of file */
