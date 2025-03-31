/**********************************************************/
/* Date: Mon, 10 Mar 1997 07:38:18 -0500                  */
/* From: Roy Longbottom <Roy_Longbottom@compuserve.com>   */
/* Subject: WHET02.txt                                    */
/* To: "Alfred A. Aburto Jr." <aburto@cts.com>            */
/**********************************************************/

#include <math.h>
#include <printf.h>
#include <stdint.h>

#include "whetstone.h"

// Axelera verbose output
#define AXE_WHETSTONE_VERBOSE

#ifdef DP
union ufloat {
  double f;
  uint64_t u;
  int64_t i;
};
typedef int64_t udiff_t;
typedef union ufloat ufloat_t;
#else
union ufloat {
  float f;
  uint32_t u;
  int32_t i;
};
typedef int32_t udiff_t;
typedef union ufloat ufloat_t;
#endif

// use different set of result for Precision and Fused (FMA) operations
#if defined(DP) && defined(FUSED)
#define REF_ENTRY(SECTION, DP, SP, FUSED_DP, FUSED_SP) (FUSED_DP)
#elif defined(DP) && !defined(FUSED)
#define REF_ENTRY(SECTION, DP, SP, FUSED_DP, FUSED_SP) (DP)
#elif defined(FUSED)
#define REF_ENTRY(SECTION, DP, SP, FUSED_DP, FUSED_SP) (FUSED_SP)
#else
#define REF_ENTRY(SECTION, DP, SP, FUSED_DP, FUSED_SP) (SP)
#endif

static SPDP_HEX refarr[] = {
    // REF_ENTRY(                   DP,         SP,           FUSED DP,   FUSED SP),
    REF_ENTRY(0, 0x0000000000000000, 0x00000000, 0x0000000000000000, 0x00000000),  // dummy entry
    REF_ENTRY(1, 0xbff221bfacf75748, 0xbf910e3f, 0xbff221bfacf75748, 0xbf910e3f),
    REF_ENTRY(2, 0xbff221a967e913f2, 0xbf910d98, 0xbff221a967e913f4, 0xbf910d98),
    REF_ENTRY(3, 0x0000000000000000, 0x00000000, 0x0000000000000000, 0x00000000),
    REF_ENTRY(4, 0x4028000000000000, 0x41400000, 0x4028000000000000, 0x41400000),
    REF_ENTRY(5, 0x3fdfffd840b68fc9, 0x3efffed8, 0x3fdfffd840b68fc9, 0x3efffed7),
    REF_ENTRY(6, 0x3fefffffc44b4b1a, 0x3f7ffffd, 0x3fefffffc44b4997, 0x3f7ffffd),
    REF_ENTRY(7, 0x4008000000000000, 0x40400000, 0x4008000000000000, 0x40400000),
    REF_ENTRY(8, 0x3fe800150a49c850, 0x3f4000ba, 0x3fe800150a49c851, 0x3f4000b9),
};

void check_whetstone_double(SPDP checknum, int section) {
  ufloat_t unit_result, unit_ref;
  unit_result.f = checknum;
  unit_ref.u = refarr[section];
  double error = fabs(unit_result.f - unit_ref.f);
  if (!CHECK_TRUE(error <= ALLOWED_ERROR)) {
    printf("  Error %e > %e\n", error, ALLOWED_ERROR);
    printf("  Expected 0x" SPDP_HEX_FMT " -> %.25f\n", unit_ref.u, unit_ref.f);
    printf("  Actual   0x" SPDP_HEX_FMT " -> %.25f\n", unit_result.u, unit_result.f);
  }
}

/**********************************************************/

void run_whetstone_checks(long xtra, long x100) {
  long n1, n2, n3, n4, n5, n6, n7, n8, i, ix, n1mult;
  SPDP x, y, z;
  long j, k, l;
  SPDP e1[4];

  SPDP t = FCONST(0.49999975);
  SPDP t0 = t;
  SPDP t1 = FCONST(0.50000025);
  SPDP t2 = FCONST(2.0);

  n1 = 12 * x100;
  n2 = 14 * x100;
  n3 = 345 * x100;
  n4 = 210 * x100;
  n5 = 32 * x100;
  n6 = 899 * x100;
  n7 = 616 * x100;
  n8 = 93 * x100;
  n1mult = 10;

  // for (i = 0; i < 7; i++)
  //   printf("test %lx\n", refarr[i]);

  /* Section 1, Array elements (N1 floating point) */
#ifdef AXE_WHETSTONE_VERBOSE
  printf("Section 1, Array elements (N1 floating point)\n");
#endif
  e1[0] = FCONST(1.0);
  e1[1] = FCONST(-1.0);
  e1[2] = FCONST(-1.0);
  e1[3] = FCONST(-1.0);
  {
    for (ix = 0; ix < xtra; ix++) {
      for (i = 0; i < n1 * n1mult; i++) {
        e1[0] = (e1[0] + e1[1] + e1[2] - e1[3]) * t;
        e1[1] = (e1[0] + e1[1] - e1[2] + e1[3]) * t;
        e1[2] = (e1[0] - e1[1] + e1[2] + e1[3]) * t;
        e1[3] = (-e1[0] + e1[1] + e1[2] + e1[3]) * t;
      }
      t = FCONST(1.0) - t;
    }
    t = t0;
  }
  check_whetstone_double(e1[3], 1);

  /* Section 2, Array as parameter (N2 floating point) */
#ifdef AXE_WHETSTONE_VERBOSE
  printf("Section 2, Array as parameter (N2 floating point)\n");
#endif
  {
    for (ix = 0; ix < xtra; ix++) {
      for (i = 0; i < n2; i++) {
        pa(e1, t, t2);
      }
      t = FCONST(1.0) - t;
    }
    t = t0;
  }
  check_whetstone_double(e1[3], 2);

#ifdef AXE_WHETSTONE_VERBOSE
  printf("Section 3, Conditional jumps\n");
#endif
  /* Section 3, Conditional jumps */
  j = 1;
  {
    for (ix = 0; ix < xtra; ix++) {
      for (i = 0; i < n3; i++) {
        if (j == 1)
          j = 2;
        else
          j = 3;
        if (j > 2)
          j = 0;
        else
          j = 1;
        if (j < 1)
          j = 1;
        else
          j = 0;
      }
    }
  }
  check_whetstone_double((SPDP)(j), 3);

#ifdef AXE_WHETSTONE_VERBOSE
  printf("Section 4, Integer arithmetic\n");
#endif
  /* Section 4, Integer arithmetic */
  j = 1;
  k = 2;
  l = 3;
  {
    for (ix = 0; ix < xtra; ix++) {
      for (i = 0; i < n4; i++) {
        j = j * (k - j) * (l - k);
        k = l * k - (l - j) * k;
        l = (l - k) * (k + j);
        e1[l - 2] = j + k + l;
        e1[k - 2] = j * k * l;
      }
    }
  }
  x = e1[0] + e1[1];
  check_whetstone_double(x, 4);

#ifdef AXE_WHETSTONE_VERBOSE
  printf("Section 5, Trig functions\n");
#endif
  /* Section 5, Trig functions */
  x = FCONST(0.5);
  y = FCONST(0.5);
  {
    for (ix = 0; ix < xtra; ix++) {
      for (i = 1; i < n5; i++) {
        x = t * atan(t2 * sin(x) * cos(x) / (cos(x + y) + cos(x - y) - FCONST(1.0)));
        y = t * atan(t2 * sin(y) * cos(y) / (cos(x + y) + cos(x - y) - FCONST(1.0)));
      }
      t = FCONST(1.0) - t;
    }
    t = t0;
  }
  check_whetstone_double(y, 5);

#ifdef AXE_WHETSTONE_VERBOSE
  printf("Section 6, Procedure calls\n");
#endif
  /* Section 6, Procedure calls */
  x = FCONST(1.0);
  y = FCONST(1.0);
  z = FCONST(1.0);
  {
    for (ix = 0; ix < xtra; ix++) {
      for (i = 0; i < n6; i++) {
        p3(&x, &y, &z, t, t1, t2);
      }
    }
  }
  check_whetstone_double(z, 6);

#ifdef AXE_WHETSTONE_VERBOSE
  printf("Section 7, Array refrences\n");
#endif
  /* Section 7, Array refrences */
  j = 0;
  k = 1;
  l = 2;
  e1[0] = FCONST(1.0);
  e1[1] = FCONST(2.0);
  e1[2] = FCONST(3.0);
  {
    for (ix = 0; ix < xtra; ix++) {
      for (i = 0; i < n7; i++) {
        po(e1, j, k, l);
      }
    }
  }
  check_whetstone_double(e1[2], 7);

#ifdef AXE_WHETSTONE_VERBOSE
  printf("Section 8, Standard functions\n");
#endif
  /* Section 8, Standard functions */
  x = FCONST(0.75);
  {
    for (ix = 0; ix < xtra; ix++) {
      for (i = 0; i < n8; i++) {
        x = sqrt(exp(log(x) / t1));
      }
    }
  }
  check_whetstone_double(x, 8);

  return;
}

void pa(SPDP e[4], SPDP t, SPDP t2) {
  long j;
  for (j = 0; j < 6; j++) {
    e[0] = (e[0] + e[1] + e[2] - e[3]) * t;
    e[1] = (e[0] + e[1] - e[2] + e[3]) * t;
    e[2] = (e[0] - e[1] + e[2] + e[3]) * t;
    e[3] = (-e[0] + e[1] + e[2] + e[3]) / t2;
  }

  return;
}

void po(SPDP e1[4], long j, long k, long l) {
  e1[j] = e1[k];
  e1[k] = e1[l];
  e1[l] = e1[j];
  return;
}

void p3(SPDP* x, SPDP* y, SPDP* z, SPDP t, SPDP t1, SPDP t2) {
  *x = *y;
  *y = *z;
  *x = t * (*x + *y);
  *y = t1 * (*x + *y);
  *z = (*x + *y) / t2;
  return;
}
