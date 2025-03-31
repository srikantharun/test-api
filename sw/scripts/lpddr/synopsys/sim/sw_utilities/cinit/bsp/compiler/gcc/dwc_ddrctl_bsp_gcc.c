// ------------------------------------------------------------------------------
// 
// Copyright 2024 Synopsys, INC.
// 
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
//            Inclusivity and Diversity" (Refer to article 000036315 at
//                        https://solvnetplus.synopsys.com)
// 
// Component Name   : DWC_ddrctl_lpddr54
// Component Version: 1.60a-lca00
// Release Type     : LCA
// Build ID         : 0.0.0.0.TreMctl_302.DwsDdrChip_8.26.6.DwsDdrctlTop_5.12.7
// ------------------------------------------------------------------------------


#include "dwc_ddrctl_bsp_gcc.h"
#include "dwc_cinit_os_bsp.h"
#include "dwc_cinit_log.h"

#define __USE_GNU
#include <link.h>

static int __attribute__((no_instrument_function)) callback(struct dl_phdr_info *info, size_t size, void *data)
{
    int p_type;
    int j;


    if (strstr(info->dlpi_name, "libcinit") == NULL) {
        return 0;
    }
     
    for (j = 0; j < info->dlpi_phnum; j++) {
        p_type = info->dlpi_phdr[j].p_type;
        if (p_type == PT_LOAD) {
            SNPS_CALL_TRACE("ADDR| %14p 0x%jx\n",
                    (void *) (info->dlpi_addr + info->dlpi_phdr[j].p_vaddr),
                    (uintmax_t) info->dlpi_phdr[j].p_memsz);
        }
    }
    return 0;
}

void __attribute__((constructor, no_instrument_function)) trace_begin(void)
{
    ddr_bsp_log_file_create(SNPS_CALL_TRACE_LOG);
    dl_iterate_phdr(callback, NULL);
}


void __attribute__((destructor, no_instrument_function)) trace_end(void)
{
    ddr_bsp_log_file_close(SNPS_CALL_TRACE_LOG);
}


void __cyg_profile_func_enter(void* this_fn, void* call_site)
{
    SNPS_CALL_TRACE("ENTR| %p %p %lu", this_fn, call_site, time(NULL));
}


void __cyg_profile_func_exit(void* this_fn, void* call_site)
{
    SNPS_CALL_TRACE("EXIT| %p %p %lu", this_fn, call_site, time(NULL));
}
