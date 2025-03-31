// See LICENSE for license details.

#ifdef __clang__
#pragma clang attribute push(__attribute__((noinline)), apply_to=function)
#else
#pragma GCC optimize("no-inline")
#endif

#include <alloca.h>

#include "dhrystone.h"
#include <testutils.h>

/* Global Variables: */
// NOTE(mwipfli): Changed "global" variables to be thread-local to allow
//                simulatneous execution of Dhrystone on multiple cores.
__thread Rec_Pointer Ptr_Glob, Next_Ptr_Glob;
__thread int Int_Glob;
__thread Boolean Bool_Glob;
__thread char Ch_1_Glob, Ch_2_Glob;
__thread int Arr_1_Glob[50];
__thread int Arr_2_Glob[50][50];



/* Dhrystone functions: */

void Proc_1(Rec_Pointer Ptr_Val_Par)
    /******************/
/* executed once */
{
  Rec_Pointer Next_Record = Ptr_Val_Par->Ptr_Comp;
  /* == Ptr_Glob_Next */
  /* Local variable, initialized with Ptr_Val_Par->Ptr_Comp,    */
  /* corresponds to "rename" in Ada, "with" in Pascal           */

  *Ptr_Val_Par->Ptr_Comp = *Ptr_Glob;
  Ptr_Val_Par->variant.var_1.Int_Comp = 5;
  Next_Record->variant.var_1.Int_Comp = Ptr_Val_Par->variant.var_1.Int_Comp;
  Next_Record->Ptr_Comp = Ptr_Val_Par->Ptr_Comp;
  Proc_3(&Next_Record->Ptr_Comp);
  if (Next_Record->Discr == Ident_1)
  /* then, executed */
  {
    Next_Record->variant.var_1.Int_Comp = 6;
    Proc_6(Ptr_Val_Par->variant.var_1.Enum_Comp, &Next_Record->variant.var_1.Enum_Comp);
    Next_Record->Ptr_Comp = Ptr_Glob->Ptr_Comp;
    Proc_7(Next_Record->variant.var_1.Int_Comp, 10, &Next_Record->variant.var_1.Int_Comp);
  } else /* not executed */
    *Ptr_Val_Par = *Ptr_Val_Par->Ptr_Comp;
} /* Proc_1 */

void Proc_2(One_Fifty* Int_Par_Ref)
    /******************/
    /* executed once */
    /* *Int_Par_Ref == 1, becomes 4 */
{
  One_Fifty Int_Loc;
  Enumeration Enum_Loc;

  Int_Loc = *Int_Par_Ref + 10;
  do /* executed once */
    if (Ch_1_Glob == 'A')
    /* then, executed */
    {
      Int_Loc -= 1;
      *Int_Par_Ref = Int_Loc - Int_Glob;
      Enum_Loc = Ident_1;
    }                          /* if */
  while (Enum_Loc != Ident_1); /* true */
} /* Proc_2 */

void Proc_3(Rec_Pointer* Ptr_Ref_Par)
    /******************/
    /* executed once */
    /* Ptr_Ref_Par becomes Ptr_Glob */
{
  if (Ptr_Glob != Null) /* then, executed */
    *Ptr_Ref_Par = Ptr_Glob->Ptr_Comp;
  Proc_7(10, Int_Glob, &Ptr_Glob->variant.var_1.Int_Comp);
} /* Proc_3 */

void Proc_4() /* without parameters */
/*******/
/* executed once */
{
  Boolean Bool_Loc;

  Bool_Loc = Ch_1_Glob == 'A';
  Bool_Glob = Bool_Loc | Bool_Glob;
  Ch_2_Glob = 'B';
} /* Proc_4 */

void Proc_5() /* without parameters */
/*******/
/* executed once */
{
  Ch_1_Glob = 'A';
  Bool_Glob = false;
} /* Proc_5 */

void Proc_6(Enumeration Enum_Val_Par, Enumeration* Enum_Ref_Par)
    /*********************************/
    /* executed once */
    /* Enum_Val_Par == Ident_3, Enum_Ref_Par becomes Ident_2 */
{
  *Enum_Ref_Par = Enum_Val_Par;
  if (!Func_3(Enum_Val_Par)) /* then, not executed */
    *Enum_Ref_Par = Ident_4;
  switch (Enum_Val_Par) {
    case Ident_1:
      *Enum_Ref_Par = Ident_1;
      break;
    case Ident_2:
      if (Int_Glob > 100) /* then */
        *Enum_Ref_Par = Ident_1;
      else
        *Enum_Ref_Par = Ident_4;
      break;
    case Ident_3: /* executed */
      *Enum_Ref_Par = Ident_2;
      break;
    case Ident_4:
      break;
    case Ident_5:
      *Enum_Ref_Par = Ident_3;
      break;
  } /* switch */
} /* Proc_6 */

void Proc_7(One_Fifty Int_1_Par_Val, One_Fifty Int_2_Par_Val, One_Fifty* Int_Par_Ref)
    /**********************************************/
    /* executed three times                                      */
    /* first call:      Int_1_Par_Val == 2, Int_2_Par_Val == 3,  */
    /*                  Int_Par_Ref becomes 7                    */
    /* second call:     Int_1_Par_Val == 10, Int_2_Par_Val == 5, */
    /*                  Int_Par_Ref becomes 17                   */
    /* third call:      Int_1_Par_Val == 6, Int_2_Par_Val == 10, */
    /*                  Int_Par_Ref becomes 18                   */
{
  One_Fifty Int_Loc;

  Int_Loc = Int_1_Par_Val + 2;
  *Int_Par_Ref = Int_2_Par_Val + Int_Loc;
} /* Proc_7 */

void Proc_8(Arr_1_Dim Arr_1_Par_Ref, Arr_2_Dim Arr_2_Par_Ref, int Int_1_Par_Val, int Int_2_Par_Val)
    /*********************************************************************/
    /* executed once      */
    /* Int_Par_Val_1 == 3 */
    /* Int_Par_Val_2 == 7 */
{
  One_Fifty Int_Index;
  One_Fifty Int_Loc;

  Int_Loc = Int_1_Par_Val + 5;
  Arr_1_Par_Ref[Int_Loc] = Int_2_Par_Val;
  Arr_1_Par_Ref[Int_Loc + 1] = Arr_1_Par_Ref[Int_Loc];
  Arr_1_Par_Ref[Int_Loc + 30] = Int_Loc;
  for (Int_Index = Int_Loc; Int_Index <= Int_Loc + 1; ++Int_Index)
    Arr_2_Par_Ref[Int_Loc][Int_Index] = Int_Loc;
  Arr_2_Par_Ref[Int_Loc][Int_Loc - 1] += 1;
  Arr_2_Par_Ref[Int_Loc + 20][Int_Loc] = Arr_1_Par_Ref[Int_Loc];
  Int_Glob = 5;
} /* Proc_8 */

Enumeration Func_1(Capital_Letter Ch_1_Par_Val, Capital_Letter Ch_2_Par_Val)
/*************************************************/
/* executed three times                                         */
/* first call:      Ch_1_Par_Val == 'H', Ch_2_Par_Val == 'R'    */
/* second call:     Ch_1_Par_Val == 'A', Ch_2_Par_Val == 'C'    */
/* third call:      Ch_1_Par_Val == 'B', Ch_2_Par_Val == 'C'    */
{
  Capital_Letter Ch_1_Loc;
  Capital_Letter Ch_2_Loc;

  Ch_1_Loc = Ch_1_Par_Val;
  Ch_2_Loc = Ch_1_Loc;
  if (Ch_2_Loc != Ch_2_Par_Val) /* then, executed */
    return (Ident_1);
  else /* not executed */
  {
    Ch_1_Glob = Ch_1_Loc;
    return (Ident_2);
  }
} /* Func_1 */

Boolean Func_2(Str_30 Str_1_Par_Ref, Str_30 Str_2_Par_Ref)
/*************************************************/
/* executed once */
/* Str_1_Par_Ref == "DHRYSTONE PROGRAM, 1'ST STRING" */
/* Str_2_Par_Ref == "DHRYSTONE PROGRAM, 2'ND STRING" */
{
  One_Thirty Int_Loc;
  Capital_Letter Ch_Loc;

  Int_Loc = 2;
  while (Int_Loc <= 2) /* loop body executed once */
    if (Func_1(Str_1_Par_Ref[Int_Loc], Str_2_Par_Ref[Int_Loc + 1]) == Ident_1)
    /* then, executed */
    {
      Ch_Loc = 'A';
      Int_Loc += 1;
    }                                /* if, while */
  if (Ch_Loc >= 'W' && Ch_Loc < 'Z') /* then, not executed */
    Int_Loc = 7;
  if (Ch_Loc == 'R') /* then, not executed */
    return (true);
  else /* executed */
  {
    if (strcmp(Str_1_Par_Ref, Str_2_Par_Ref) > 0)
    /* then, not executed */
    {
      Int_Loc += 7;
      Int_Glob = Int_Loc;
      return (true);
    } else /* executed */
      return (false);
  } /* if Ch_Loc */
} /* Func_2 */

Boolean Func_3(Enumeration Enum_Par_Val)
/***************************/
/* executed once        */
/* Enum_Par_Val == Ident_3 */
{
  Enumeration Enum_Loc;

  Enum_Loc = Enum_Par_Val;
  if (Enum_Loc == Ident_3) /* then, executed */
    return (true);
  else /* not executed */
    return (false);
} /* Func_3 */



/* Main dhrystone verification function: */

void run_dhrystone_checks()
{
  /* Local variables */
  One_Fifty Int_1_Loc;
  One_Fifty Int_2_Loc;
  One_Fifty Int_3_Loc;
  char Ch_Index;
  Enumeration Enum_Loc;
  Str_30 Str_1_Loc;
  Str_30 Str_2_Loc;
  int Run_Index;
  int Number_Of_Runs;

  /* Arguments */
  Number_Of_Runs = 1;

  /* Initializations */
  Next_Ptr_Glob = (Rec_Pointer)alloca(sizeof(Rec_Type));
  Ptr_Glob = (Rec_Pointer)alloca(sizeof(Rec_Type));

  Ptr_Glob->Ptr_Comp = Next_Ptr_Glob;
  Ptr_Glob->Discr = Ident_1;
  Ptr_Glob->variant.var_1.Enum_Comp = Ident_3;
  Ptr_Glob->variant.var_1.Int_Comp = 40;
  strcpy(Ptr_Glob->variant.var_1.Str_Comp, "DHRYSTONE PROGRAM, SOME STRING");
  strcpy(Str_1_Loc, "DHRYSTONE PROGRAM, 1'ST STRING");

  Arr_2_Glob[8][7] = 10;

  for (Run_Index = 1; Run_Index <= Number_Of_Runs; ++Run_Index) {
    Proc_5();
    Proc_4();
    /* Ch_1_Glob == 'A', Ch_2_Glob == 'B', Bool_Glob == true */
    Int_1_Loc = 2;
    Int_2_Loc = 3;
    strcpy(Str_2_Loc, "DHRYSTONE PROGRAM, 2'ND STRING");
    Enum_Loc = Ident_2;
    Bool_Glob = !Func_2(Str_1_Loc, Str_2_Loc);
    /* Bool_Glob == 1 */
    while (Int_1_Loc < Int_2_Loc) /* loop body executed once */
    {
      Int_3_Loc = 5 * Int_1_Loc - Int_2_Loc;
      /* Int_3_Loc == 7 */
      Proc_7(Int_1_Loc, Int_2_Loc, &Int_3_Loc);
      /* Int_3_Loc == 7 */
      Int_1_Loc += 1;
    } /* while */
    /* Int_1_Loc == 3, Int_2_Loc == 3, Int_3_Loc == 7 */
    Proc_8(Arr_1_Glob, Arr_2_Glob, Int_1_Loc, Int_3_Loc);
    /* Int_Glob == 5 */
    Proc_1(Ptr_Glob);
    for (Ch_Index = 'A'; Ch_Index <= Ch_2_Glob; ++Ch_Index)
    /* loop body executed twice */
    {
      if (Enum_Loc == Func_1(Ch_Index, 'C'))
      /* then, not executed */
      {
        Proc_6(Ident_1, &Enum_Loc);
        strcpy(Str_2_Loc, "DHRYSTONE PROGRAM, 3'RD STRING");
        Int_2_Loc = Run_Index;
        Int_Glob = Run_Index;
      }
    }
    /* Int_1_Loc == 3, Int_2_Loc == 3, Int_3_Loc == 7 */
    Int_2_Loc = Int_2_Loc * Int_1_Loc;
    Int_1_Loc = Int_2_Loc / Int_3_Loc;
    Int_2_Loc = 7 * (Int_2_Loc - Int_3_Loc) - Int_1_Loc;
    /* Int_1_Loc == 1, Int_2_Loc == 13, Int_3_Loc == 7 */
    Proc_2(&Int_1_Loc);
    /* Int_1_Loc == 5 */

  } /* loop "for Run_Index" */

  CHECK_TRUE(Int_Glob == 5);
  CHECK_TRUE(Bool_Glob == 1);
  CHECK_TRUE(Ch_1_Glob == 'A');
  CHECK_TRUE(Ch_2_Glob == 'B');
  CHECK_TRUE(Arr_1_Glob[8] == 7);
  CHECK_TRUE(Arr_2_Glob[8][7] == Number_Of_Runs + 10);
  // Note: Check for Ptr_Glob->Ptr_Comp is implementation-dependent and was omitted
  CHECK_TRUE(Ptr_Glob->Discr == 0);
  CHECK_TRUE(Ptr_Glob->variant.var_1.Enum_Comp == 2);
  CHECK_TRUE(Ptr_Glob->variant.var_1.Int_Comp == 17);
  CHECK_TRUE(strcmp(Ptr_Glob->variant.var_1.Str_Comp, "DHRYSTONE PROGRAM, SOME STRING") == 0);
  // Note: Check for Next_Ptr_Glob->Ptr_Comp is implementation-dependent and was omitted
  CHECK_TRUE(Next_Ptr_Glob->Discr == 0);
  CHECK_TRUE(Next_Ptr_Glob->variant.var_1.Enum_Comp == 1);
  CHECK_TRUE(Next_Ptr_Glob->variant.var_1.Int_Comp == 18);
  CHECK_TRUE(strcmp(Next_Ptr_Glob->variant.var_1.Str_Comp, "DHRYSTONE PROGRAM, SOME STRING") == 0);
  CHECK_TRUE(Int_1_Loc == 5);
  CHECK_TRUE(Int_2_Loc == 13);
  CHECK_TRUE(Int_3_Loc == 7);
  CHECK_TRUE(Enum_Loc == 1);
  CHECK_TRUE(strcmp(Str_1_Loc, "DHRYSTONE PROGRAM, 1'ST STRING") == 0);
  CHECK_TRUE(strcmp(Str_2_Loc, "DHRYSTONE PROGRAM, 2'ND STRING") == 0);
}

#ifdef __clang__
#pragma clang attribute pop
#endif
