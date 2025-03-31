#!/usr/bin/env python3


import argparse
import os
import sys
import subprocess as sp
import re
import ujson as json
from pathlib import Path
from typing import Tuple, Type, List


class DisassemblyInfo:
    def __init__(self) -> None:
        self.start_address_to_function_name: dict[int, str] = {}
        self.return_address_to_function_name: dict[int, str] = {}
        self.address_to_line_number: dict[str, int] = {}
        self.regex_pattern_address = re.compile(r"^([0-9A-Fa-f]+):")
        self.regex_pattern_fn_label = re.compile("^# ([a-zA-Z0-9_]+):$")

    def parse_disassembly_file(self, path: Path) -> None:
        with open(path, "r") as fp:
            in_function = False
            function_str = "UNKNOWN"
            next_line_is_func_entry = False
            for ln, line in enumerate(fp):
                line = line.strip()
                m_addr = self.regex_pattern_address.match(line)
                if m_addr:
                    address_str = m_addr.group(1)
                    self.address_to_line_number[address_str] = ln + 1
                    if next_line_is_func_entry:
                        in_function = True
                        address = int(address_str, 16)
                        self.start_address_to_function_name[address] = function_str
                        next_line_is_func_entry = False
                if len(line) and line[0] == "#":
                    m_fn_label = self.regex_pattern_fn_label.match(line)
                    if m_fn_label:
                        function_str = m_fn_label.group(1)
                        if next_line_is_func_entry:
                            raise ValueError("Found two successive asm labels without a source line in-between")
                        next_line_is_func_entry = True
                    continue
                elif line.find(">:") != -1:
                    in_function = True
                    address_str, function_str = line.split()
                    address = int(address_str, 16)
                    function_str = function_str[:-1].lstrip("<").rstrip(">")
                    self.start_address_to_function_name[address] = function_str
                elif in_function and line[-3:] == "ret":
                    address_str = line.split(":")[0]
                    address = int(address_str, 16)
                    self.return_address_to_function_name[address] = function_str
                elif line == "...":
                    continue


class FunctionCall:
    call_level = 0

    def __init__(self, function_name: str) -> None:
        self.function_name = function_name
        self.call_level = -1
        self.start_line = -1
        self.start_time = -1
        self.end_line = -1
        self.end_time = -1

    def begin(self, start_line: int, start_time: int = -1) -> "FunctionCall":
        FunctionCall.call_level += 1
        self.call_level = FunctionCall.call_level
        self.start_line = start_line
        self.start_time = start_time
        return self

    def end(self, end_line: int, end_time: int = -1) -> "FunctionCall":
        FunctionCall.call_level -= 1
        self.end_line = end_line
        self.end_time = end_time
        return self

    def get_exec_time(self) -> int:
        if self.start_time == -1 or self.end_time == -1:
            return 0
        return self.end_time - self.start_time

    def to_dict(self):
        return {"start_line": self.start_line, "end_line": self.end_line, "time": self.get_exec_time()}


def list_to_str_deduplicated(values: list[str]) -> str:
    values_with_count: list[list] = []
    for value in values:
        if values_with_count and values_with_count[-1][0] == value:
            values_with_count[-1][1] += 1
        else:
            values_with_count.append([value, 1])
    values_str: list[str] = []
    for value, count in values_with_count:
        if count == 1:
            values_str.append(value)
        else:
            values_str.append(f"{value} ({count}x)")
    return ", ".join(values_str)


class InstructionDumpInfo:
    def __init__(self, asm: DisassemblyInfo) -> None:
        self.asm = asm
        self.function_calls_info: list[str] = []
        self.function_calls_dict: dict[str, list[FunctionCall]] = {}
        self.line_number_to_address_and_time: dict[int, tuple[str, int] | None] = {}
        # TODO: Redefine this in your child class
        # Index in a line where each instruction address starts
        # Assumes that the dump file respects some kind of formatting/padding
        # This is mostly a QoL for nvim
        self.inst_address_index = 0

    def addr2line(self, bin_path: Path, address_str: str) -> str:
        return sp.getoutput(f"riscv64-unknown-elf-addr2line -e {bin_path} {address_str}")

    def print_function_calls_info(self) -> None:
        print("\n".join(self.function_calls_info))

    def print_function_exec_times(self) -> None:
        if not self.function_calls_dict:
            print("no function calls found")
            return
        max_func_chars = max([len(fn) for fn in self.function_calls_dict])
        for function_name in self.function_calls_dict:
            exec_times = [fc.get_exec_time() for fc in self.function_calls_dict[function_name]]
            print(f"{function_name:{max_func_chars}}: {exec_times}")

    def write_json_file(
        self,
        json_path: Path,
        hart_id: int,
        bin_path: Path,
        inst_dump_path: Path,
        disassembly_path: Path,
    ):
        function_calls = {}
        for fname, fcalls in self.function_calls_dict.items():
            formatted_fcalls = []
            for fcall in fcalls:
                formatted_fcalls.append(fcall.to_dict())
            function_calls[fname] = formatted_fcalls

        file_content = {
            "hart_id": hart_id,
            "bin_path": f"{bin_path.absolute()}",
            "inst_dump_path": f"{inst_dump_path.absolute()}",
            "disassembly_path": f"{disassembly_path.absolute()}",
            "inst_addr_col": self.inst_address_index,
            "function_calls": function_calls,
            "line_number_to_address_and_time": self.line_number_to_address_and_time,
            "disassembly_address_to_line_number": self.asm.address_to_line_number,
        }

        with open(json_path, "w+") as fp:
            json.dump(file_content, fp, separators=(",", ":"))
            # DEBUG: json.dump(file_content, fp, indent=2)

    def parse_dump_line(self, line: str) -> Tuple[int, int | None]:
        # TODO: Implement this function to parse the lines of your dump log
        ...

    def parse_dump_file(self, inst_dump_path: Path, bin_path: Path | None = None, print_file_and_line=False) -> None:
        with open(inst_dump_path, "r") as fp:
            dict_start_addr_to_func = self.asm.start_address_to_function_name
            dict_return_addr_to_func = self.asm.return_address_to_function_name
            fc_list: list[FunctionCall] = []
            time, ln = 0, 0

            for ln, line in enumerate(fp):
                time_tmp, address = self.parse_dump_line(line)
                if address is None:
                    self.line_number_to_address_and_time[ln + 1] = (None, None)
                    continue

                # only update time on valid lines, useful for fc_dict_push of remaining calls
                time = time_tmp
                address_str = f"{hex(address)}"[2:]

                # line info
                self.line_number_to_address_and_time[ln + 1] = (address_str, time)

                # function info
                if address in dict_start_addr_to_func:
                    function_name = dict_start_addr_to_func[address]
                    instr_info = function_name
                    if bin_path and print_file_and_line:
                        file_line_info = self.addr2line(bin_path, address_str)
                        instr_info = f"{function_name} {file_line_info}"
                    self.function_calls_info.append(f"{time}: {address_str} {instr_info}")
                    fc = FunctionCall(function_name).begin(ln, time)
                    fc_list.append(fc)
                if address in dict_return_addr_to_func and len(fc_list) >= 1:
                    function_name = dict_return_addr_to_func[address]
                    unwound_fcs = []
                    unwind_nb = None
                    for i,fc in enumerate(reversed(fc_list)):
                        if fc.function_name == function_name:
                            unwind_nb = i
                            break
                    if unwind_nb is None:
                        # Handle cases where we branched directly into into a function
                        # past its start address. This can happend when dealing with inline asssembly
                        # e.g. Andes tests
                        print(f"Warning, returning from {function_name} without having entered it!")
                    elif unwind_nb > 0 :
                        # Unwind function calls if required:
                        # This can happen for two reasons:
                        # - tail calls (which are not supported correctly)
                        # - non-calling jumps to the first line in a function (e.g., because of a loop)
                        for unwound_fc in reversed(fc_list[len(fc_list) - unwind_nb:]):
                            unwound_fcs.append(unwound_fc.function_name)
                            self.function_calls_dict.setdefault(unwound_fc.function_name, [])
                            self.function_calls_dict[unwound_fc.function_name].append(unwound_fc.end(ln, time))
                        fc_list = fc_list[:len(fc_list) - unwind_nb]
                    if unwound_fcs:
                        print(
                            f"unwound {len(unwound_fcs)} calls to make call stack consistent again:",
                            list_to_str_deduplicated(unwound_fcs),
                        )
                    fc = fc_list.pop()
                    self.function_calls_dict.setdefault(function_name, [])
                    self.function_calls_dict[function_name].append(fc.end(ln, time))

        # fc_dict_push remaining calls are the ones which never returned
        for fc in fc_list:
            self.function_calls_dict.setdefault(fc.function_name, [])
            self.function_calls_dict[fc.function_name].append(fc.end(ln, time))


class Ax65InstructionDumpInfo(InstructionDumpInfo):
    """Parse AX65 instruction dumps"""

    def __init__(self, asm: DisassemblyInfo) -> None:
        super().__init__(asm)
        self.inst_address_index = 28
        self.regex_pattern_time = re.compile(r"^\d+")

    def parse_dump_line(self, line: str) -> Tuple[int, int | None]:
        time = 0
        address = None
        line = line.strip()
        array = line.split(":")

        # "special" line: reset, exception, resume, etc
        if len(array) != 4 or line.find(":@") == -1:
            self.function_calls_info.append(line)
        else:
            # normal lines
            time_str, _, _, inst_str = array

            # get read of any decimals or timestamp unit
            m = self.regex_pattern_time.match(time_str)
            if m:
                time_str = m.group(0)
            else:
                raise ValueError("Time is not formatted properly")

            time = int(time_str)
            address_str = inst_str[1:17]
            address = int(address_str, 16)
        return time, address


class CVA6VSpikeInstructionDumpInfo(InstructionDumpInfo):
    """Parse CVA6V and Spike instruction dumps"""

    def __init__(self, asm: DisassemblyInfo) -> None:
        super().__init__(asm)
        self.inst_address_index = 16
        # emulation: [t=1234] ; simulation: [t=1234.00 ns]
        self.regex_pattern_time = re.compile(r"t=(\d+)")

    def parse_dump_line(self, line: str) -> Tuple[int, int | None]:
        time = 0
        address = None
        line = line.strip()
        array = line.split()

        # instruction line
        if line[0:5] == "core " and ">>>>" not in line and "exception" not in line and "tval" not in line:
            # time: "[t=1234]" is not always present
            try:
                m = self.regex_pattern_time.match(line.split("[")[1])
                time = int(m.group(1))
            except:
                time = 0
            address_str = array[2]
            address = int(address_str, 16)

        return time, address


class CVA6VInternalTraceInstructionDumpInfo(InstructionDumpInfo):
    """Parse CVA6V internal instruction dumps"""

    def __init__(self, asm: DisassemblyInfo) -> None:
        super().__init__(asm)
        self.inst_address_index = 16

    def parse_dump_line(self, line: str) -> Tuple[int, int | None]:
        time = 0
        address = None
        line = line.strip()
        array = line.split()

        # instruction line
        if "INVALID" not in line and "Exception" not in line and "tval" not in line:
            try:
                time_str = array[0][:-2]
                time = int(time_str)
            except:
                time = 0
            address_str = array[3]
            address = int(address_str, 16)

        return time, address


def print_banner(msg: str) -> None:
    print("#---------------------------------------------------")
    print(f"# {msg}")
    print("#---------------------------------------------------")


def get_disassembly_path() -> Path:
    disassembly_paths = list(Path(".").glob("*.S"))
    if len(disassembly_paths) == 0:
        raise FileNotFoundError("No disassembly file found in current directory!")
    elif len(disassembly_paths) > 1:
        raise FileNotFoundError("Found multiple disassembly files in current directory!")
    return disassembly_paths[0]


def get_bin_path(disassembly_path: Path) -> Path:
    bin_path = disassembly_path.with_suffix("")
    if not bin_path.exists():
        raise FileNotFoundError(f"Binary file {bin_path} not found!")
    return bin_path


def get_inst_dump_path(hart_id: int) -> Path:
    inst_dump_paths = list(Path(".").glob(f"instruction_dump_*_id{hart_id}.log"))
    if len(inst_dump_paths) == 0:
        raise FileNotFoundError("No dump file found!")
    elif len(inst_dump_paths) > 1:
        raise FileNotFoundError("Found multiple dump files in current directory!")
    return inst_dump_paths[0]


def guess_inst_dump_info(
    dump_info_types: List[Type[InstructionDumpInfo]],
    asm: DisassemblyInfo,
    inst_dump_path: Path,
) -> InstructionDumpInfo:
    max_success_rate = 0.0
    best_dump_info = None
    with open(inst_dump_path, "r") as fp:
        for dump_info_cls in dump_info_types:
            dump_info = dump_info_cls(asm)
            addr_count = 0
            count = 0
            fp.seek(0)
            for line in fp:
                count += 1
                # Parse at most the first 20 lines
                if count == 20:
                    break
                try:
                    _, address = dump_info.parse_dump_line(line)
                    if address is not None:
                        addr_count += 1
                except:
                    continue
            if count == 0:
                raise ValueError("Dump file is empty!")
            success_rate = addr_count / count
            if success_rate > max_success_rate:
                best_dump_info = dump_info
                max_success_rate = success_rate

    if best_dump_info is None:
        raise ValueError("No InstructionDumpInfo found!")

    return best_dump_info


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="print digest FW trace info",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    )
    parser.add_argument("-i", "--hart_id", type=int, nargs="*", help="CPU hart id", default=[0])
    parser.add_argument(
        "-l",
        "--print_file_and_line",
        action="store_true",
        help="print file name and line number next to the addresses",
    )
    parser.add_argument(
        "-n",
        "--nvim",
        action="store_true",
        help="start nvim in disassembly inspector mode",
    )
    parser.add_argument(
        "-N",
        "--nvim_no_gen",
        action="store_true",
        help="like --nvim but skip the parsing and file generation",
    )
    parser.add_argument(
        "-f",
        "--nvim_fast",
        action="store_true",
        help="like --nvim but with no fancy colors etc",
    )
    parser.add_argument(
        "--nvim_line",
        type=int,
        help="jump at this line in the dump file at startup",
    )
    parser.add_argument(
        "--nvim_gen_info_only",
        action="store_true",
        help="generate all info needed by nvim without running nvim",
    )
    parser.add_argument("-g", "--glyphs", action="store_true", help="display glyphs on buttons")
    args = parser.parse_args()

    nvim = args.nvim or args.nvim_line or args.nvim_gen_info_only or args.nvim_no_gen or args.nvim_fast

    disassembly_path = get_disassembly_path()
    bin_path = get_bin_path(disassembly_path)

    inst_dump_json_files = []
    for hart_id in args.hart_id:
        inst_dump_path = get_inst_dump_path(hart_id)
        inst_dump = None
        if not args.nvim_no_gen:
            asm = DisassemblyInfo()
            asm.parse_disassembly_file(disassembly_path)
            inst_dump_types = [
                Ax65InstructionDumpInfo,
                CVA6VSpikeInstructionDumpInfo,
                CVA6VInternalTraceInstructionDumpInfo,
            ]
            inst_dump = guess_inst_dump_info(inst_dump_types, asm, inst_dump_path)
            inst_dump.parse_dump_file(inst_dump_path, bin_path, args.print_file_and_line)

        if nvim:
            os.makedirs(".fw_trace_utils", exist_ok=True)
            inst_dump_json_file_name = inst_dump_path.with_suffix(".json").name
            inst_dump_json_path = Path(f".fw_trace_utils/{inst_dump_json_file_name}")
            inst_dump_json_files.append(inst_dump_json_path)
            if inst_dump:
                inst_dump.write_json_file(inst_dump_json_path, hart_id, bin_path, inst_dump_path, disassembly_path)
        elif inst_dump:
            print_banner("function calls")
            inst_dump.print_function_calls_info()
            print("")
            print_banner("function exec times")
            inst_dump.print_function_exec_times()

    if nvim:
        fw_trace_utils_lua_setup = Path(os.environ["REPO_ROOT"]) / "sw/scripts/nvim/fw_trace_utils/setup.lua"
        fw_trace_utils_lua_pre = Path(os.environ["REPO_ROOT"]) / "sw/scripts/nvim/fw_trace_utils/pre.lua"
        fw_trace_utils_lua_require = Path(f".fw_trace_utils/fw_trace_utils_requires.lua")
        with open(fw_trace_utils_lua_require, "w+") as fp:
            fp.write("_G.fw_trace_utils_info = {\n")
            fp.write(
                f"enable_glyphs = {'true' if (args.glyphs or 'FW_TRACE_UTILS_GLYPHS' in os.environ) else 'false'},\n"
            )
            fp.write(f"initial_jump_line = {args.nvim_line or 'nil'},\n")
            fp.write("hart_info = {\n")
            for file_path in inst_dump_json_files:
                fp.write(f"  '{file_path.absolute()}',\n")
            fp.write("}}\n")
        if args.nvim_gen_info_only:
            exit(0)
        extra_nvim_args = ""
        if args.nvim_fast:
            extra_nvim_args = "--clean"
        while True:
            nvim_cmd_line = f"module switch nvim/0.10.2; nvim {extra_nvim_args} -S {fw_trace_utils_lua_pre} -S {fw_trace_utils_lua_require} -S {fw_trace_utils_lua_setup}"
            sp.run(nvim_cmd_line, shell=True)
            # reload fw_trace_utils if reload_file is created
            reload_file = Path(".fw_trace_utils_reload")
            if reload_file.exists():
                nvim_line = reload_file.read_text().strip()

                # filter original cmd line
                args_to_be_removed = ("--nvim_no_gen", "-N")
                cmd_line_org = " ".join([arg for arg in sys.argv if arg not in args_to_be_removed])

                sp.run(f"{cmd_line_org} --nvim_line {nvim_line} --nvim_gen_info_only", shell=True)
                reload_file.unlink(missing_ok=True)  # in case nvim crashes
            else:
                break
