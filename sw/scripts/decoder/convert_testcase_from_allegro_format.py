#!/usr/bin/env python3
# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Owner:       Max Wipfli <max.wipfli@axelera.ai>
# Description: Converts testcases from the format for the Allegro decoder
#              testbench so they can be played using C code from the APU.
import os
import re
import sys
from argparse import ArgumentParser
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import TextIO


@dataclass
class Buffer:
    data: bytes
    load_addr: int
    full_len: int


def div_ceil(x, y):
    return -(x // -y)


def parse_args():
    parser = ArgumentParser()
    parser.add_argument(
        "input",
        type=Path,
        help="testcase input directory (containing instructions.hex and *.mem files)",
    )
    return parser.parse_args()


def parse_readmemh_single_buffer(
    lines: list[str], strip_trailing_zeros: bool = False
) -> Buffer:
    # parse address
    m = re.match(r"^@([0-9A-Fa-f]+)", lines[0])
    if m is None:
        # no address specified
        word_addr = 0
    else:
        # parse hex address
        word_addr = int(m.group(1), 16)
        # remove address line
        lines.pop(0)

    # parse data
    parsed = [bytes.fromhex(line.replace("_", "")) for line in lines]
    # convert endianness
    reversed = [line[::-1] for line in parsed]

    # check all lines are the same number of bytes
    bytes_per_line = set(len(line) for line in reversed)
    assert len(bytes_per_line) == 1, "All data lines are the same length."
    byte_addr = word_addr * next(iter(bytes_per_line))

    full_buf = b"".join(reversed)
    if strip_trailing_zeros:
        # Make sure the buffer size is 32-byte aligned and there are at least
        # 32 zero bytes at the end, as the actual data may end with a few
        # zeros.
        last_nonzero_idx = -1
        for i, byte in enumerate(full_buf):
            if byte != 0:
                last_nonzero_idx = i
        buf_end_idx = div_ceil(last_nonzero_idx, 32) * 32
        buf_end_idx += 32
        buf_end_idx = min(len(full_buf), buf_end_idx)
        buf = full_buf[:buf_end_idx]
    else:
        buf = full_buf

    return Buffer(buf, load_addr=byte_addr, full_len=len(full_buf))


def parse_readmemh_file(
    input: Path, strip_trailing_zeros: bool = False
) -> list[Buffer]:
    with input.open("r") as f:
        groups = []
        current_group = []

        for line in f:
            if line.strip().startswith("//"):
                # comment line
                continue
            if line.startswith("@"):
                # address line, start of new group
                if current_group:
                    groups.append(current_group)
                    current_group = []
            current_group.append(line.strip())

        if current_group:
            groups.append(current_group)

    return [
        parse_readmemh_single_buffer(group, strip_trailing_zeros=strip_trailing_zeros)
        for group in groups
    ]


def parse_allegro_instructions(input_dir: Path) -> list[tuple[str, str, str]]:
    """Returns a list of tuples: (instruction, address/process, value/frame, comment)"""
    inst_path = input_dir / "instructions.hex"
    instructions = []
    with inst_path.open("r") as f:
        for line in f:
            m = re.match(r"^(\w+),[0-9.]*,(\w*),(\w*),\d*,* *// (.*)$", line.rstrip("\n"))
            instructions.append(m.groups())
    return instructions


def parse_allegro_in_buffers(input_dir: Path) -> list[(str, int, Buffer)]:
    """Returns a list of tuples: (frame_process, frame_idx, Buffer)"""
    buffers = []
    for buf_path in sorted(input_dir.glob("*.mem")):
        print(f"Parsing input buffers: {buf_path.name}")
        m = re.match("sram_([0-9]+)\.(.*)\.mem", buf_path.name)
        frame_idx, frame_process = m.groups()
        frame_idx = int(frame_idx)

        # Strip trailing zeros from buffers:
        # Makes the sizes of the input buffers reasonable, as they are always
        # generated as 32 MB blobs, with 99% of them being 0.
        strip_trailing_zeros = frame_process != "MCU"

        file_buffers = parse_readmemh_file(
            buf_path, strip_trailing_zeros=strip_trailing_zeros
        )
        buffers.extend((frame_process, frame_idx, buf) for buf in file_buffers)
    return buffers


def parse_allegro_refmap(refmap_file: Path) -> list[(str, int)]:
    """Returns a list of tuples: (buffer_name, address)"""
    if refmap_file.name == "sram_0000.MCU.refmap":
        print("Skipping *.refmap for MCU")
        return []
    print(f"Parsing *.refmap: {refmap_file.name}")
    entries = []
    with refmap_file.open("r") as f:
        for line in f:
            line = line.rstrip("\n")
            if not line:
                continue
            parts = line.split(" ")
            assert len(parts) == 3, "invalid format for *.refmap"
            buf_name = parts[0]
            buf_addr = int(parts[1], 16)
            # discard the third value (length)
            entries.append((buf_name, buf_addr))
    return entries


def parse_allegro_ref_buffers(input_dir: Path) -> list[(str, int, Buffer)]:
    """Returns a list of tuples: (frame_process, frame_idx, Buffer)"""
    buffers = []
    for refmap_path in sorted(input_dir.glob("*.refmap")):
        entries = parse_allegro_refmap(refmap_path)
        m = re.match("sram_([0-9]+)\.(.*)\.refmap", refmap_path.name)
        frame_idx, frame_process = m.groups()
        frame_idx = int(frame_idx)

        for buf_name, load_addr in entries:
            buf_path = refmap_path.parent / f"{refmap_path.stem}.ref.{buf_name}"
            print(f"Parsing reference output buffers: {buf_path.name}")
            bufs = parse_readmemh_file(buf_path)
            assert len(bufs) == 1, "*.ref.out.* contains multiple buffers"
            buf = bufs[0]
            buf.load_addr = load_addr
            buffers.append((frame_process, frame_idx, buf))
    return buffers


def emit_c_file_header(out: TextIO, in_dir: Path):
    script_name = Path(__file__).name
    in_dir = str(in_dir.resolve())
    try:
        in_dir = in_dir.replace(os.environ["REPO_ROOT"], "$REPO_ROOT")
    except KeyError:
        pass
    out.write("// (C) Copyright Axelera AI {}\n".format(datetime.now().year))
    out.write("// All Rights Reserved\n")
    out.write("// *** Axelera AI Confidential ***\n")
    out.write("//\n")
    out.write(f"// Owner: {script_name}\n")
    out.write(f"// Testcase input directory: {in_dir}\n")
    out.write("//\n")
    out.write("// This file has been automatically generated. DO NOT MODIFY!\n")
    out.write("\n")
    out.write("#include <decoder/decoder_testcase.h>\n")


def emit_c_bytearray(out: TextIO, data: bytes, symbol_name: str):
    out.write("__attribute__((aligned(64)))\n")
    out.write(f"static char {symbol_name}[] = {{\n")

    LINE_WIDTH = 16
    for i, byte in enumerate(data):
        if i % LINE_WIDTH == 0:
            out.write("  ")
        out.write(f"0x{byte:02x}")
        if i == len(data) - 1:
            out.write("\n")
            break
        out.write(",")
        if i % LINE_WIDTH == LINE_WIDTH - 1:
            out.write("\n")
        else:
            out.write(" ")
    out.write("};\n")


def emit_allegro_testcase_instructions(
    out: TextIO, instructions: list[tuple[str, str, str]], array_name: str
) -> tuple[str, int]:
    out.write(f"static struct decoder_testcase_instruction {array_name}[] = {{\n")
    for name, address_or_process, value_or_frame, comment in instructions:
        enum_name = f"DECODER_TESTCASE_INSTRUCTION_{name.upper()}"
        address = "0"
        data = "0"
        frame_process = "NULL"
        frame_idx = "0"
        irq_address = "0"
        irq_bit = "0"
        if name == "write":
            address = address_or_process
            data = value_or_frame
        elif name == "start_frame" or name == "end_frame":
            frame_process = f'"{address_or_process}"'
            frame_idx = value_or_frame
        elif name == "irq":
            irq_address = address_or_process
            irq_bit = value_or_frame
        out.write(
            f"  {{ {enum_name}, {address}, {data}, {frame_process}, {frame_idx}, {irq_address}, {irq_bit} }}, // {comment}\n"
        )
    out.write("};\n")
    return array_name, len(instructions)


def emit_allegro_testcase_buffers(out: TextIO, buffers: list, array_name: str):
    for i, (_, _, buf) in enumerate(buffers):
        buffer_name = f"{array_name}_{i:03d}"
        emit_c_bytearray(out, buf.data, buffer_name)
        out.write("\n")

    out.write(f"static struct decoder_testcase_buffer {array_name}[] = {{\n")
    for i, (frame_process, frame_idx, buf) in enumerate(buffers):
        buffer_name = f"{array_name}_{i:03d}"
        out.write(
            f'  {{ "{frame_process}", {frame_idx}, (void*){buffer_name}, {len(buf.data)}, {buf.full_len}, 0x{buf.load_addr:010x} }},\n'
        )
    out.write("};\n")


def emit_allegro_testcase(
    input_dir: Path,
    output_file: Path,
    instructions: list,
    in_buffers: list,
    ref_buffers: list,
    struct_symbol: str,
):
    instructions_symbol = f"__{struct_symbol}_instructions"
    in_buffers_symbol = f"__{struct_symbol}_in_buffers"
    ref_buffers_symbol = f"__{struct_symbol}_ref_buffers"

    with output_file.open("w") as f:
        emit_c_file_header(f, input_dir)
        f.write("\n")

        emit_allegro_testcase_instructions(f, instructions, instructions_symbol)
        f.write("\n")

        emit_allegro_testcase_buffers(f, in_buffers, in_buffers_symbol)
        f.write("\n")

        emit_allegro_testcase_buffers(f, ref_buffers, ref_buffers_symbol)
        f.write("\n")

        f.write(f"struct decoder_testcase {struct_symbol} = {{\n")
        f.write(f"  {instructions_symbol},\n")
        f.write(f"  {len(instructions)},\n")
        f.write(f"  {in_buffers_symbol},\n")
        f.write(f"  {len(in_buffers)},\n")
        f.write(f"  {ref_buffers_symbol},\n")
        f.write(f"  {len(ref_buffers)},\n")
        f.write("};\n")


def main() -> int:
    args = parse_args()

    testcase_name = args.input.resolve().name
    instructions = parse_allegro_instructions(args.input)
    in_buffers = parse_allegro_in_buffers(args.input)
    ref_buffers = parse_allegro_ref_buffers(args.input)

    emit_allegro_testcase(
        args.input,
        args.input / f"{testcase_name}.c",
        instructions,
        in_buffers,
        ref_buffers,
        "testcase",
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
