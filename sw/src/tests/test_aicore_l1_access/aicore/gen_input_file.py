#!/usr/bin/env python3

from pathlib import Path

AICORE_NB = 8
L1_BASE_ADDRESS = "0x{}8000000"
L1_SIZE = 0x400000

for aicore in range(AICORE_NB):
    format_string = f"{{:016x}}"
    file_path = Path(__file__).parent / f"aicore{aicore}_l1_buffer.c"
    print(f"Generating: {file_path}")
    with open(file_path, "w+") as f:
        f.write("#include <stdint.h>\n\n")
        f.write(f'uint64_t l1_buffer[{L1_SIZE//8}] __attribute__((section(".l1")))= {{\n')
        base_address = int(L1_BASE_ADDRESS.format(aicore+1), 16)
        for offset in range(0, L1_SIZE, 16):
            address = base_address + offset
            # set the value to the address
            lsb_hex_address = format_string.format(address)
            msb_hex_address = format_string.format(address + 8)
            f.write(f"  0x{lsb_hex_address}u, 0x{msb_hex_address}u,\n")
        f.write("};\n")
