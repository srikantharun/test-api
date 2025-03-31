#!/bin/sh
# (C) Copyright Axelera AI 2024
# All Rights Reserved
# *** Axelera AI Confidential ***
#
# Description: Script to build and package LLVM/Clang 18 toolchain.
# Owner:       Max Wipfli <max.wipfli@axelera.ai>
#
# This has been adapted from the toolchain build in the Makefile of:
# https://github.com/axelera-ai/hw.riscv/

set -eu

TOOLCHAIN_LLVM_VERSION="18.1.7"
TOOLCHAIN_LLVM_DIR="llvm-project-$TOOLCHAIN_LLVM_VERSION.src"
TOOLCHAIN_LLVM_FILE="$TOOLCHAIN_LLVM_DIR.tar.xz"
TOOLCHAIN_LLVM_URL="https://github.com/llvm/llvm-project/releases/download/llvmorg-$TOOLCHAIN_LLVM_VERSION/$TOOLCHAIN_LLVM_FILE"
TOOLCHAIN_LLVM_SHA256="74446ab6943f686391954cbda0d77ae92e8a60c432eff437b8666e121d748ec4"

show_help () {
  cat << EOF
Usage: $(basename "$0") [ARGS]
Fetch, build, and package LLVM/Clang toolchain for RV64.

-h, --help              show this help
-b, --build [build_dir] select build directory (default: ./build)
-f, --fetch-only        only fetch tarballs (do not build)

Offline Build
-------------
To build the toolchain on an isolated machine, perform the following steps:
  1. On an Internet-connected machine, fetch the required tarballs.
       $ $(basename "$0") --fetch-only
  2. Copy the tarballs from the online machine's build directory (default:
       ./build) to the offline machines's build directory.
  3. Build the toolchain on the offline machine. The previously fetched tarballs
       will be used automatically. If the script attempts to download anything,
       this means the tarballs are not located at the correct place.
       $ $(basename "$0")
EOF
}

fetch() {
  fetch_file="$1"
  fetch_url="$2"
  fetch_sha256="$3"
  fetch_path="$build_dir/$fetch_file"

  if [ -f "$fetch_path" ]; then
    echo "[+] File $fetch_file already exists locally, skipping fetch..."
  else
    echo "[+] Fetching $fetch_file from $fetch_url..."
    wget -O "$fetch_path" "$fetch_url"
  fi
  actual_sha256="$(sha256sum "$fetch_path" | cut -d ' ' -f1)"

  if [ "$actual_sha256" = "$fetch_sha256" ]; then 
    echo "[+] File $fetch_file has correct checksum."
  else
    echo "[-] Error: Checksum mismatch for file $fetch_file."
    exit 1
  fi
}

build_toolchain_llvm() {
  cd "$build_dir"
  # Unpacking files
  echo "[+] Unpacking LLVM source tarball..."
  rm -rf "$TOOLCHAIN_LLVM_DIR"
  tar -xf "$TOOLCHAIN_LLVM_FILE"
  # Configure
  echo "[+] Configuring LLVM..."
  cd "$TOOLCHAIN_LLVM_DIR"
  cmake -S llvm -B build \
    -DCMAKE_BUILD_TYPE="Release"                       \
    -DBUILD_SHARED_LIBS=True                           \
    -DLLVM_USE_SPLIT_DWARF=True                        \
    -DCMAKE_INSTALL_PREFIX="$package_dir"              \
    -DLLVM_OPTIMIZED_TABLEGEN=True                     \
    -DLLVM_BUILD_TESTS=False                           \
    -DLLVM_DEFAULT_TARGET_TRIPLE="riscv64-unknown-elf" \
    -DLLVM_TARGETS_TO_BUILD="RISCV"                    \
    -DLLVM_ENABLE_PROJECTS="clang;lld"                 \
  # Build and install
  echo "[+] Building and installing LLVM..."
  cmake --build build -j"$(nproc)" --target install
  # Removing unpacked files and build artifacts
  echo "[+] Removing LLVM build artifacts..."
  cd "$build_dir"
  rm -rf "$TOOLCHAIN_LLVM_DIR"
}

package () {
  echo "[+] Packaging toolchain..."
  cd "$(dirname "$package_dir")"
  tar -czf "$package_tarball" "$(basename "$package_dir")"
}

# Option parsing with getopt
options=$(getopt -o 'hbf' --long 'help,build:,fetch-only' -- "$@")

eval set -- "$options"

# Default values for options
do_fetch_only=0
build_dir="$(realpath ./build)"

# Parse options
while true; do
  case "$1" in
    -h | --help)
      show_help
      exit 0
      shift
      ;;
    -b | --build)
      build_dir="$2"
      shift 2
      ;;
    -f | --fetch-only)
      do_fetch_only=1
      shift
      ;;
    -- )
      shift
      break
      ;;
    * )
      echo "Error: Option declared but not handled."
      exit 1
      ;;
  esac
done

# Set further variables needed for the build
package_name="riscv64-unknown-elf-toolchain-llvm-axelera"
package_dir="$build_dir/$package_name"
package_tarball="$build_dir/$package_name.tar.gz"

# Force using gcc/g++ explicitly instead of cc/c++. This is required as the GCC
# compiler from Modules does not include symlinks for cc/c++, which makes CMake
# fall back to the system compiler (/usr/bin/{cc,c++}), which may be too old.
export CC=gcc
export CXX=g++

# Prepare build and package directories
mkdir -p "$build_dir"
rm -rf "$package_dir"
mkdir -p "$package_dir"

# Fetch
fetch "$TOOLCHAIN_LLVM_FILE" "$TOOLCHAIN_LLVM_URL" "$TOOLCHAIN_LLVM_SHA256"

if [ "$do_fetch_only" -eq 1 ]; then
  echo "[+] Fetch complete. Output: $build_dir"
  exit 0
fi

# Build toolchain
build_toolchain_llvm

# Package
package

echo "[+] Toolchain has been built. Output: $package_tarball"
