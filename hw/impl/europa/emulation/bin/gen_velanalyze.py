#!/usr/bin/env python3


import argparse
import subprocess
from pathlib import Path
import json
import os

# Default bender targets
BENDER_TARGETS = ["rtl", "emulation", "asic", "sf5a",]
REPO_ROOT = os.environ['REPO_ROOT']


def run_bash(cmd_str):
    return subprocess.run(cmd_str.split(), stdout=subprocess.PIPE)


def get_bender_output(directory, targets):
    targets_str = " ".join([f"-t {t}" for t in targets])
    run_bash(f"bender -d {directory} update")
    p = run_bash(f"bender -d {directory} sources {targets_str} -f")
    return p.stdout


class FileList:
    def __init__(self,
                 print_info=True,
                 bender_dir= Path(""),
                 bender_targets= [],
                 output_dir= Path(""),
                 global_defines = []
                 ):
        self.print_info = print_info
        self.bender_dir = bender_dir
        self.bender_targets = bender_targets
        self.output_dir = output_dir
        self.global_defines = global_defines
        # init values
        self.bender_output = b''
        # files
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.f_json = (self.output_dir / "bender.json").open("w")
        self.f_run_velana = (self.output_dir / "run_velanalyze.sh").open("w")


    def get_source_files(self, package) -> list[Path]:
        src_paths = []
        for src in package['files']:
            path = Path(src).resolve()
            if not path.exists():
                raise Exception(f"path {path} does not exist in package {package['package']}")
            src_paths.append(path)
        return src_paths


    def get_defines(self, package) -> dict:
        defines = {f"TARGET_{t.upper()}":None for t in self.bender_targets}
        for define in self.global_defines:
            defines[define] = None
        for var in package['defines']:
            val = package['defines'][var]
            if var in defines and defines[var] != val:
                raise Exception(f"define {var} exists with 2 different values {val} and {defines[var]}")
            defines[var] = val
        return defines


    def get_inc_dirs(self, package):
        inc_dirs = []
        inc_dirs += package['include_dirs']
        for export_name in package['export_incdirs']:
            inc_dirs += package['export_incdirs'][export_name]
        for dir in inc_dirs:
            path = Path(dir).resolve()
            if not path.exists():
                raise Exception(f"inc_dir {path} does not exist in package {package['package']}")
        return inc_dirs

    def write_velanalyze(self, package):
        veloce_analyze_dir = "veloce_rundir"
        lib_name = package["package"]
        source_files = self.get_source_files(package)
        inc_dirs = self.get_inc_dirs(package)
        defines = self.get_defines(package)
        source_files_str = " \\\n  ".join([f"{src}" for src in source_files if src.suffix not in [".vhd", ".vhdp"]])
        vhdl_source_files_str = " \\\n  ".join([f"{src}" for src in source_files if src.suffix in [".vhd", ".vhdp"]])
        inc_dirs_str = " \\\n  ".join([f"+incdir+{dir}" for dir in inc_dirs])
        defines_str = ""
        for var in defines:
            defines_str += f"  +define+{var}"
            val = defines[var]
            if val:
                defines_str += f"={val}"
            defines_str += " \\\n"
        self.f_run_velana.write(f"mkdir -p {veloce_analyze_dir}\n")
        self.f_run_velana.write(f"vellib {veloce_analyze_dir}/{lib_name}\n")
        self.f_run_velana.write(f"velmap {lib_name} {veloce_analyze_dir}/{lib_name}\n")
        self.f_run_velana.write(f"velanalyze -sv -mfcu -work {lib_name}\\\n{defines_str}  {inc_dirs_str} \\\n  {source_files_str}\n\n")
        if vhdl_source_files_str:
            vhdl_lib_name = f"vhdl_{lib_name}"
            self.f_run_velana.write(f"vellib {veloce_analyze_dir}/{vhdl_lib_name}\n")
            self.f_run_velana.write(f"velmap {vhdl_lib_name} {veloce_analyze_dir}/{vhdl_lib_name}\n")
            self.f_run_velana.write(f"velanalyze -hdl vhdl -permissive -mfcu -work {vhdl_lib_name}\\\n{defines_str}  {inc_dirs_str} \\\n  {vhdl_source_files_str}\n\n")


    def parse_bender_and_write_files(self):
        self.bender_output = get_bender_output(self.bender_dir, self.bender_targets)

        self.f_json.write(self.bender_output.decode())

        self.f_run_velana.write("#!/usr/bin/env bash\n\n")
        self.f_run_velana.write("set -e\n\n")
        for package in json.loads(self.bender_output):
            self.write_velanalyze(package)


if __name__ == "__main__":
    # argument parsing
    parser = argparse.ArgumentParser(description="generate filelist for top-level emulation",
                                     formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    parser.add_argument( '--bender_dir', type=Path, help='location of Bender.yml')
    parser.add_argument( '--output_dir', type=Path, help='location of output directory', default='./filelists')
    parser.add_argument('--global_define', action='append', help='add a global define', default=[])
    parser.add_argument('--no_softmodel', action='store_true', help='if specified, remove softmodels from compilation flow')
    args = parser.parse_args()
    bender_targets = BENDER_TARGETS

    if args.no_softmodel == False:
        bender_targets += ["spinor_s25fs512s", "emmc_softmodel"]

    fl = FileList(bender_dir=args.bender_dir, bender_targets=bender_targets, output_dir=args.output_dir, global_defines=args.global_define)
    fl.parse_bender_and_write_files()
