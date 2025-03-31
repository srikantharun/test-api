import argparse
import os
import pathlib
import subprocess

def scan_directory_for_asm_files(directory, pattern='*.S'):
    """ Ignores objdumps in build/ folder by default """
    build_folder = directory / "build"
    return [a for a in directory.rglob(pattern) if build_folder not in a.parents]

def execute_command(cmd, verbose=False):
    result = subprocess.run(cmd, shell=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if verbose:
        print(f"\n Executed command: {cmd}, subprocess result: {result.stdout}")
    if result.returncode != 0:
        print(f"Error: {result.stdout}")
    return result.returncode == 0

def compile_to_elf(asm, args):
    elf = args.output_dir / asm.stem
    cmd = f"riscv64-unknown-elf-gcc -O0 {asm} -T {args.linker_file} {args.gcc_options} -I {args.gcc_includes} -o {elf} -march={args.arch} -mabi=lp64f"
    return execute_command(cmd, args.verbose)

def generate_objdump(asm, args):
    elf = args.output_dir / asm.stem
    cmd = f"riscv64-unknown-elf-objdump -d {elf} > {elf}_objdump.S"
    return execute_command(cmd, args.verbose)

def parse_arguments():
    repo_root = os.environ.get('REPO_ROOT')
    parser = argparse.ArgumentParser(description="Scan .S files and generate elfs in build/.")
    parser.add_argument("--input_dir", type=pathlib.Path, default=".", help="The directory to scan for .S files.")
    parser.add_argument("--output_dir", type=pathlib.Path, default="./build/", help="The output build/ path.")
    parser.add_argument("--arch", type=str, default="rv64imafc_zicsr_zifencei_zve32f_zfh_zfhmin", help="Architecture to build on")
    parser.add_argument("--linker_file", type=str, help="GCC Linker path", default=f"{repo_root}/sw/src/lib/cva6v/link.ld")
    parser.add_argument("--gcc_options", type=str, help="GCC options", default='-nostdlib -nostartfiles -mno-strict-align')
    parser.add_argument("--gcc_includes", type=str, help="GCC includes", default='../../env')
    parser.add_argument("--objdump", action='store_true', help="Generate objdump alongside the elf")
    parser.add_argument("--verbose", action='store_true', help="Prints each executed command")

    return parser.parse_args()

def main(args):
    asms = scan_directory_for_asm_files(args.input_dir)
    if not args.output_dir.exists():
        args.output_dir.mkdir(parents=True, exist_ok=True)
    for asm in asms:
        compile_to_elf(asm, args)
        if args.objdump:
            generate_objdump(asm, args)

if __name__ == "__main__":
    args = parse_arguments()
    main(args)
