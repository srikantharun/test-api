#!/usr/bin/env python3

from pathlib import Path

L2_BASE = 0x000008000000
L2_SIZE = 0x000008000000

# data = addr
format_string = f"{{:016x}}"
file_path = Path(__file__).parent / "l2_buffer.c"
print(f"Generating: {file_path}")
with open(file_path, "w+") as f:
    f.write("#include <stdint.h>\n\n")
    f.write(f'uint64_t l2_buffer[{L2_SIZE//8}] __attribute__((section(".l2")))= {{\n')
    for addr_8B in range(L2_SIZE//8):
        value = L2_BASE + addr_8B*8
        f.write(f"  0x{value:016x}u,\n")
    f.write("};\n")
