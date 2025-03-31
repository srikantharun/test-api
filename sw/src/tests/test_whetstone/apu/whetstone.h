/*
 * These files are a modified version of the sources found here:
 * subip/common/ax25_ae350/andes_vip/patterns/samples/test_whetstone_v5/whet.c
 *
 * As we only use whetstone for verification, we did the following modifications:
 *  - Strip down all the generic stuff we don't need
 *  - The whole time measurement/benchmark logic was removed
 *  - Only one run, enough for verification
 *  - Instead of outputting the result, register result and add debug prints
 *
 * The core logic of whetstone was not modified at all! Same types, same variables,
 * same functions and same expected results.
 */

#ifndef _WHETSTONE_H
#define _WHETSTONE_H

#include <string.h>
#include <testutils.h>

/**********************************************************/
/* Configuration                                          */
/**********************************************************/

#define DP              // enable to use double (instead of float)

/**********************************************************/

#ifdef DP
#define SPDP double
#define SPDP_HEX uint64_t
#define Precision "Double"
#define FCONST(c) (c)  // default is double
#define SPDP_HEX_FMT "%016lx"
#define ALLOWED_ERROR 1e-13
#else
#define SPDP float
#define SPDP_HEX uint32_t
#define Precision "Single"
#define atan atanf
#define sin sinf
#define cos cosf
#define sqrt sqrtf
#define exp expf
#define log logf
#define FCONST(c) (c##F)  // declare as single constant
#define SPDP_HEX_FMT "%08x"
#define ALLOWED_ERROR 1e-13
#endif

/* Wrapper for all whetstone checks */
void check_whetstone_double(SPDP checknum, int section);

/* Main whetstone verification function: */
void run_whetstone_checks(long xtra, long x100);

/* actual whetstone functions, core logic not changed, only the result evaluation */
void pa(SPDP e[4], SPDP t, SPDP t2);
void po(SPDP e1[4], long j, long k, long l);
void p3(SPDP* x, SPDP* y, SPDP* z, SPDP t, SPDP t1, SPDP t2);

#endif // _WHETSTONE_H
