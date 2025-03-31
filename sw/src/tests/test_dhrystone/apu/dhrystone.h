/*
 * These files are a modified version of the sources found here:
 * https://github.com/riscv-software-src/riscv-tests/tree/master/benchmarks/dhrystone
 *
 * Dhrystone version: C, Version 2.2
 *
 * As we only use dhrystone for verification, we did the following modifications:
 *  - Structure/content of the files to have cleaner interface and allow a simple main
 *  - All define-parameters removed, not used and more overview
 *  - The whole time measurement/benchmark logic was removed
 *  - Only one run, enough for verification
 *
 * The core logic of dhrystone was not modified at all! Same types, same variables,
 * same functions and same expected results.
 */

#ifndef _DHRYSTONE_H
#define _DHRYSTONE_H

#include <string.h>

/* General definitions: */

#define Null 0
#define true 1
#define false 0

typedef int One_Thirty;
typedef int One_Fifty;
typedef char Capital_Letter;
typedef int Boolean;
typedef char Str_30[31];
typedef int Arr_1_Dim[50];
typedef int Arr_2_Dim[50][50];

typedef enum { Ident_1, Ident_2, Ident_3, Ident_4, Ident_5 } Enumeration;

typedef struct record {
  struct record* Ptr_Comp;
  Enumeration Discr;
  union {
    struct {
      Enumeration Enum_Comp;
      int Int_Comp;
      char Str_Comp[31];
    } var_1;
    struct {
      Enumeration E_Comp_2;
      char Str_2_Comp[31];
    } var_2;
    struct {
      char Ch_1_Comp;
      char Ch_2_Comp;
    } var_3;
  } variant;
} Rec_Type, *Rec_Pointer;

/* Dhrystone functions: */
void Proc_1(Rec_Pointer);
void Proc_2(One_Fifty*);
void Proc_3(Rec_Pointer*);
void Proc_4();
void Proc_5();
void Proc_6(Enumeration, Enumeration*);
void Proc_7(One_Fifty, One_Fifty, One_Fifty*);
void Proc_8(Arr_1_Dim, Arr_2_Dim, int, int);
Enumeration Func_1(Capital_Letter, Capital_Letter);
Boolean Func_2(Str_30, Str_30);
Boolean Func_3(Enumeration);

/* Main dhrystone verification function: */
void run_dhrystone_checks();

#endif // _DHRYSTONE_H
