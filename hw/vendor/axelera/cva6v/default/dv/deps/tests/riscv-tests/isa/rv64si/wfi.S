# See LICENSE for license details.

#*****************************************************************************
# wfi.S
#-----------------------------------------------------------------------------
#
# Test wait-for-interrupt instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64S
RVTEST_CODE_BEGIN

  # Make sure wfi doesn't halt the hart, even if interrupts are disabled
  csrc sstatus, SSTATUS_SIE
  csrs sie, SIP_SSIP
  csrs sip, SIP_SSIP
  wfi;

  # this is RVTEST PASS as in original code but added restoring of SIE/SIP/STATUS
  # as we use WIF for EOT mechanism now
  fence;
  li TESTNUM, 1;
  sw TESTNUM, tohost, t5;
  csrc sie, SIP_SSIP
  csrc sip, SIP_SSIP
  csrs sstatus, SSTATUS_SIE

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
