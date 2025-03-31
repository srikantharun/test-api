#pragma once

/* Prints the current values of all general purpose registers (x0-x31). */
__attribute__((naked)) void debug_dump_registers();
