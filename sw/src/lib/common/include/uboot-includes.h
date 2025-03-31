#pragma once

#define MEMSET(s, c, n)              __builtin_memset ((s), (c), (n))
#define MEMCPY(des, src, n)          __builtin_memcpy((des), (src), (n))


// Use stdbool instead
// typedef int bool;
// #define false 0
// #define true 1

typedef long			__kernel_ssize_t;
typedef __kernel_ssize_t	ssize_t;
typedef long long		__kernel_loff_t;
typedef __kernel_loff_t		loff_t;
typedef __SIZE_TYPE__		__kernel_size_t;
typedef __kernel_size_t		size_t;

#ifndef NULL
#define NULL 0
#endif
#define UINT_MAX	(~0U)
#define ARRAY_SIZE(x) (sizeof(x) / sizeof((x)[0]))

#define dev_dbg(fmt, ...)

/* errno.h */

#define	EIO		 5	/* I/O error */
#define	ENXIO		 6	/* No such device or address */
#define	EINVAL		22	/* Invalid argument */
#define ENOTSUPP	524	/* Operation is not supported */
#define	ETIMEDOUT	110	/* Connection timed out */
#define	EREMOTEIO	121	/* Remote I/O error */
#define	EMEDIUMTYPE	124	/* Wrong medium type */

#define MAX_ERRNO	4095
#define unlikely(x)	__builtin_expect(!!(x), 0)
#define IS_ERR_VALUE(x) unlikely((x) >= (unsigned long)-MAX_ERRNO)

/*
 * Port of riscv/include/asm/io.h
 *
 * Generic virtual read/write.  Note that we don't support half-word
 * read/writes.  We define __arch_*[bl] here, and leave __arch_*w
 * to the architecture specific code.
 *
 * SPDX-License-Identifier: GPL-2.0
 * Copyright (C) 2017 Andes Technology Corporation
 * Rick Chen, Andes Technology Corporation <rick@andestech.com>
 */
#define __arch_getb(a)			(*(volatile unsigned char *)(a))
#define __arch_getw(a)			(*(volatile unsigned short *)(a))
#define __arch_getl(a)			(*(volatile unsigned int *)(a))
#define __arch_getq(a)			(*(volatile unsigned long long *)(a))

#define __arch_putb(v, a)		(*(volatile unsigned char *)(a) = (v))
#define __arch_putw(v, a)		(*(volatile unsigned short *)(a) = (v))
#define __arch_putl(v, a)		(*(volatile unsigned int *)(a) = (v))
#define __arch_putq(v, a)		(*(volatile unsigned long long *)(a) = (v))

#define __raw_writeb(v, a)		__arch_putb(v, a)
#define __raw_writew(v, a)		__arch_putw(v, a)
#define __raw_writel(v, a)		__arch_putl(v, a)
#define __raw_writeq(v, a)		__arch_putq(v, a)

#define __raw_readb(a)			__arch_getb(a)
#define __raw_readw(a)			__arch_getw(a)
#define __raw_readl(a)			__arch_getl(a)
#define __raw_readq(a)			__arch_getq(a)

// NOTE: accordign to risc-v spec fence could be more fine grained
#define mb()        asm volatile ("fence") // fence iorw, iorw
#define wmb()       asm volatile ("fence") // fence wo, wo
#define rmb()       asm volatile ("fence") // fence ri, ri

#define dmb()		mb()
#define __iormb()	rmb()
#define __iowmb()	wmb()

/* SPDX-License-Identifier: GPL-2.0 */
/*
 * asm-generic/int-ll64.h
 *
 * Integer declarations for architectures which use "long long"
 * for 64-bit types.
 */
#ifndef __ASSEMBLY__
/*
 * __xx is ok: it doesn't pollute the POSIX namespace. Use these in the
 * header files exported to user space
 */

typedef __signed__ char __s8;
typedef unsigned char __u8;

typedef __signed__ short __s16;
typedef unsigned short __u16;

typedef __signed__ int __s32;
typedef unsigned int __u32;

#ifdef __GNUC__
__extension__ typedef __signed__ long long __s64;
__extension__ typedef unsigned long long __u64;
#else
typedef __signed__ long long __s64;
typedef unsigned long long __u64;
#endif

typedef __s8  s8;
typedef __u8  u8;
typedef __s16 s16;
typedef __u16 u16;
typedef __s32 s32;
typedef __u32 u32;
typedef __s64 s64;
typedef __u64 u64;

#endif /* __ASSEMBLY__ */

/*
 * Bitfield access macros from include/linux/bitfield.h
 *
 * Copyright (C) 2014 Felix Fietkau <nbd@nbd.name>
 * Copyright (C) 2004 - 2009 Ivo van Doorn <IvDoorn@gmail.com>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License version 2
 * as published by the Free Software Foundation
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 */
#define __bf_shf(x) (__builtin_ffsll(x) - 1)

/**
 * FIELD_PREP() - prepare a bitfield element
 * @_mask: shifted mask defining the field's length and position
 * @_val:  value to put in the field
 *
 * FIELD_PREP() masks and shifts up the value.  The result should
 * be combined with other fields of the bitfield using logical OR.
 */
#define FIELD_PREP(_mask, _val)						\
	({								\
		((typeof(_mask))(_val) << __bf_shf(_mask)) & (_mask);	\
	})

/**
 * FIELD_GET() - extract a bitfield element
 * @_mask: shifted mask defining the field's length and position
 * @_reg:  32bit value of entire bitfield
 *
 * FIELD_GET() extracts the field specified by @_mask from the
 * bitfield passed in as @_reg by masking and shifting it down.
 */
#define FIELD_GET(_mask, _reg)						\
	({								\
		(typeof(_mask))(((_reg) & (_mask)) >> __bf_shf(_mask));	\
	})


/*
 * include/linux/bitops.h
 * riscv/include/asm/types.h
 */
#ifdef CONFIG_ARCH_RV64I
#define BITS_PER_LONG 64
#else
#define BITS_PER_LONG 32
#endif
#define GENMASK(h, l) \
	(((~0UL) << (l)) & (~0UL >> (BITS_PER_LONG - 1 - (h))))
// Already defined in common/include/util.h
// #define BIT(nr)			(1UL << (nr))

# define __iomem        __attribute__((noderef, address_space(2)))


/* include/linux/kernel.h */
#define min_t(type, x, y) ({			\
	type __min1 = (x);			\
	type __min2 = (y);			\
	__min1 < __min2 ? __min1: __min2; })
#define min(x, y) ({				\
	typeof(x) _min1 = (x);			\
	typeof(y) _min2 = (y);			\
	(void) (&_min1 == &_min2);		\
	_min1 < _min2 ? _min1 : _min2; })
#define min3(x, y, z) min((typeof(x))min(x, y), z)


// asm/io.h generic read writes, __iomem removed as ignored by compiler

static inline void writeb(u8 val, volatile void *addr)
{
	__iowmb();
	__arch_putb(val, addr);
}

static inline void writew(u16 val, volatile void *addr)
{
	__iowmb();
	__arch_putw(val, addr);
}

static inline void writel(u32 val, volatile void *addr)
{
	__iowmb();
	__arch_putl(val, addr);
}

static inline u8 readb(const volatile void *addr)
{
	u8	val;

	val = __arch_getb(addr);
	__iormb();
	return val;
}

static inline u16 readw(const volatile void *addr)
{
	u16	val;

	val = __arch_getw(addr);
	__iormb();
	return val;
}

static inline u32 readl(const volatile void *addr)
{
	u32	val;

	val = __arch_getl(addr);
	__iormb();
	return val;
}
