# VerifSDK Toolchain

VerifSDK requires a C toolchain (compiler, linker, binutils, debugger) to build, analyze and debug firmware code for the various RISC-V cores in the Europa architecture.

The toolchain in use consists of:
* LLVM/Clang compiler and linker (`clang`, `lld`),
* GNU binutils (`riscv64-unknown-elf-*`),
* GNU debugger (`riscv64-unknown-elf-gdb`), and
* Newlib's `libm.a`.

> **Note:** The debugger in use may switch to LLDB in the future.

The LLVM-based toolchain is preferred by the hardware team due to its superior RISC-V Vector extension (RVV) support.
For simplicity, we use this toolchain for all RISC-V cores (i.e., also for the Andes AX65 APU cores).

We use the [Axelera RISC-V toolchain distribution], which includes GNU binutils, GCC, LLVM and GDB in a single tree.
This is built by the production software team based on a [GitHub meta repository](https://github.com/axelera-ai/tools.riscv-toolchain) and available through environment modules.
