#!/usr/bin/env python3
# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: Script to override the RISC-V float ABI in ELF file headers
# Owner:       Max Wipfli <max.wipfli@axelera.ai>
import lief
import sys
from argparse import ArgumentParser
from pathlib import Path


def parse_args():
  parser = ArgumentParser()
  parser.add_argument("abi", type=str, help="float ABI (lp64, lp64f, lp64d)")
  parser.add_argument("input", type=Path, help="input ELF file")
  parser.add_argument("output", type=Path, help="output ELF file")
  return parser.parse_args()


def patch_float_abi(elf: lief.ELF.Binary, abi: str) -> None:
  # Values taken from https://github.com/riscv-non-isa/riscv-elf-psabi-doc/blob/master/riscv-elf.adoc
  EF_RISCV_FLOAT_ABI_MASK = 0xFFFFFFF9
  EF_RISCV_FLOAT_ABI_SOFT = 0x00000000
  EF_RISCV_FLOAT_ABI_SINGLE = 0x00000002
  EF_RISCV_FLOAT_ABI_DOUBLE = 0x00000004
  # old flag value from ELF
  e_flags = elf.header.processor_flag
  # step 1: remove old float ABI bits
  e_flags &= EF_RISCV_FLOAT_ABI_MASK
  # step 2: set correct bits
  if abi == "lp64":
    e_flags |= EF_RISCV_FLOAT_ABI_SOFT
  elif abi == "lp64f":
    e_flags |= EF_RISCV_FLOAT_ABI_SINGLE
  elif abi == "lp64d":
    e_flags |= EF_RISCV_FLOAT_ABI_DOUBLE
  else:
    print(f"Error: Unsupported float ABI '{abi}'")
    sys.exit(1)
  # write back to ELF
  elf.header.processor_flag = e_flags


def main() -> int:
  args = parse_args()
  elf = lief.parse(str(args.input))
  patch_float_abi(elf, args.abi)
  elf.write(str(args.output))
  return 0


if __name__ == "__main__":
  sys.exit(main())
