// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: C++ elf loader
// Owner: Florian Zaruba <florian.zaruba@axelera.ai>

#pragma once
#include <assert.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include <cstring>
#include <iostream>
#include <map>
#include <string>
#include <vector>

#define IS_ELF(hdr) \
  ((hdr).e_ident[0] == 0x7f && (hdr).e_ident[1] == 'E' && (hdr).e_ident[2] == 'L' && (hdr).e_ident[3] == 'F')

#define IS_ELF32(hdr) (IS_ELF(hdr) && (hdr).e_ident[4] == 1)
#define IS_ELF64(hdr) (IS_ELF(hdr) && (hdr).e_ident[4] == 2)

#define PT_LOAD      1
#define SHT_NOBITS   8
#define SHT_PROGBITS 0x1
#define SHT_GROUP    0x11

typedef struct {
  uint8_t  e_ident[16];
  uint16_t e_type;
  uint16_t e_machine;
  uint32_t e_version;
  uint32_t e_entry;
  uint32_t e_phoff;
  uint32_t e_shoff;
  uint32_t e_flags;
  uint16_t e_ehsize;
  uint16_t e_phentsize;
  uint16_t e_phnum;
  uint16_t e_shentsize;
  uint16_t e_shnum;
  uint16_t e_shstrndx;
} Elf32_Ehdr;

typedef struct {
  uint32_t sh_name;
  uint32_t sh_type;
  uint32_t sh_flags;
  uint32_t sh_addr;
  uint32_t sh_offset;
  uint32_t sh_size;
  uint32_t sh_link;
  uint32_t sh_info;
  uint32_t sh_addralign;
  uint32_t sh_entsize;
} Elf32_Shdr;

typedef struct {
  uint32_t p_type;
  uint32_t p_offset;
  uint32_t p_vaddr;
  uint32_t p_paddr;
  uint32_t p_filesz;
  uint32_t p_memsz;
  uint32_t p_flags;
  uint32_t p_align;
} Elf32_Phdr;

typedef struct {
  uint32_t st_name;
  uint32_t st_value;
  uint32_t st_size;
  uint8_t  st_info;
  uint8_t  st_other;
  uint16_t st_shndx;
} Elf32_Sym;

typedef struct {
  uint8_t  e_ident[16];
  uint16_t e_type;
  uint16_t e_machine;
  uint32_t e_version;
  uint64_t e_entry;
  uint64_t e_phoff;
  uint64_t e_shoff;
  uint32_t e_flags;
  uint16_t e_ehsize;
  uint16_t e_phentsize;
  uint16_t e_phnum;
  uint16_t e_shentsize;
  uint16_t e_shnum;
  uint16_t e_shstrndx;
} Elf64_Ehdr;

typedef struct {
  uint32_t sh_name;
  uint32_t sh_type;
  uint64_t sh_flags;
  uint64_t sh_addr;
  uint64_t sh_offset;
  uint64_t sh_size;
  uint32_t sh_link;
  uint32_t sh_info;
  uint64_t sh_addralign;
  uint64_t sh_entsize;
} Elf64_Shdr;

typedef struct {
  uint32_t p_type;
  uint32_t p_flags;
  uint64_t p_offset;
  uint64_t p_vaddr;
  uint64_t p_paddr;
  uint64_t p_filesz;
  uint64_t p_memsz;
  uint64_t p_align;
} Elf64_Phdr;

typedef struct {
  uint32_t st_name;
  uint8_t  st_info;
  uint8_t  st_other;
  uint16_t st_shndx;
  uint64_t st_value;
  uint64_t st_size;
} Elf64_Sym;

template <typename ehdr_t, typename phdr_t, typename shdr_t, typename sym_t>
struct ElfBinaryData {
  const ehdr_t *eh = nullptr;
  const phdr_t *ph = nullptr;
};

struct ElfSection {
  const uint8_t *data_src;
  uint64_t       data_dst;
  size_t         data_len;
  uint64_t       zero_dst;
  size_t         zero_len;
};

struct ElfBinary {
  const uint8_t *raw  = nullptr;
  size_t         size = 0;

  const Elf64_Ehdr                                            *eh64 = nullptr;
  ElfBinaryData<Elf32_Ehdr, Elf32_Phdr, Elf32_Shdr, Elf32_Sym> data32;
  ElfBinaryData<Elf64_Ehdr, Elf64_Phdr, Elf64_Shdr, Elf64_Sym> data64;

  uint64_t                entry;
  std::vector<ElfSection> sections;

  void load() {
    assert(size >= sizeof(Elf64_Ehdr));
    eh64 = (const Elf64_Ehdr *)raw;
    assert(IS_ELF32(*eh64) || IS_ELF64(*eh64));

    if (IS_ELF32(*eh64))
      parse(data32);
    else
      parse(data64);
  }

  template <typename ehdr_t, typename phdr_t, typename shdr_t, typename sym_t>
  void parse(ElfBinaryData<ehdr_t, phdr_t, shdr_t, sym_t> &data) {
    data.eh = (const ehdr_t *)raw;
    data.ph = (const phdr_t *)(raw + data.eh->e_phoff);
    entry   = data.eh->e_entry;
    assert(size >= data.eh->e_phoff + data.eh->e_phnum * sizeof(*data.ph));
    for (unsigned i = 0; i < data.eh->e_phnum; i++) {
      if (data.ph[i].p_type == PT_LOAD && data.ph[i].p_memsz) {
        if (data.ph[i].p_filesz) {
          assert(size >= data.ph[i].p_offset + data.ph[i].p_filesz);
          sections.push_back({
              .data_src = (const uint8_t *)raw + data.ph[i].p_offset,
              .data_dst = data.ph[i].p_paddr,
              .data_len = data.ph[i].p_filesz,
              .zero_dst = data.ph[i].p_paddr + data.ph[i].p_filesz,
              .zero_len = data.ph[i].p_memsz - data.ph[i].p_filesz,
          });
        }
      }
    }
  }
};

struct ElfBinaryFile : public ElfBinary {
  const std::string filename;

  ElfBinaryFile(const char *filename) : filename(filename) {
    int         fd = open(filename, O_RDONLY);
    struct stat s;
    assert(fd != -1);
    assert(fstat(fd, &s) >= 0);
    size = s.st_size;

    raw = (uint8_t *)mmap(NULL, size, PROT_READ, MAP_PRIVATE, fd, 0);
    assert(raw != MAP_FAILED);
    close(fd);

    load();
  }

  ~ElfBinaryFile() {
    if (raw) munmap((void *)raw, size);
  }
};

struct ElfBinaryBuffer : public ElfBinary {
  ElfBinaryBuffer(const char *buffer, size_t size) {
    this->raw  = (const uint8_t *)buffer;
    this->size = size;
    load();
  }
};
