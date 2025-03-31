#pragma once

#include <stdint.h>

#define UART_DEFAULT_BAUD_RATE 115200

void setup_irq_uart(void);
char readSerial();
void writeSerial(char a);
void init_uart(uint32_t freq, uint32_t baud);
void put_buf(const char *str, const uint32_t buflen);
