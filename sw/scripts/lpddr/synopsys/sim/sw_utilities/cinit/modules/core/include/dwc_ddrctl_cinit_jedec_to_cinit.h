#ifndef __DWC_DDRCTL_CINIT_JEDEC_TO_CINIT_H__
#define __DWC_DDRCTL_CINIT_JEDEC_TO_CINIT_H__

#include "dwc_ddrctl_cinit.h"

uint32_t cinit_round_down_only_int_ddr4(uint32_t value_ps, uint32_t tck_ps);

void dwc_ddrctl_cinit_jedec_to_cinit(void);

#endif /* __DWC_DDRCTL_CINIT_JEDEC_TO_CINIT_H__ */
