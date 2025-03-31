// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
#include <memorymap.h>
#include <uvm_ipc/uvm_sw_ipc.h>
#include <testutils.h>
#include <string.h>
#include <printf.h>
#include <logging.h>
#include <pctl/drv_pctl.h>


typedef struct {
    const char* path;  // Path formatting string
    uint64_t n_pctl;   // Number of PCTL instances that follow the same path format
    uint64_t n_resets; // Number of PPMUs per PCTL
    uint64_t n_clkdiv; // Number of Clock Dividers per PCTL
    uint64_t n_fences; // Number of Fences per PCTL
    uint64_t base;     // Base address of the first PCTL
    uint64_t offset;   // Offset between PCTL bases
} pctl_info;

// Exact no. of resets, fences and clkdivs still to be determained, look at https://git.axelera.ai/prod/europa/-/issues/1851
const pctl_info pctls[] = {
    {"sim_top.i_hdl_top.i_europa.u_aipu.u_ai_core_p_%lu.u_pctl",        2, 1, 1, 1, SYS_CFG_AICORE_0_AO_CSR_BASE,    SYS_CFG_AICORE_0_AO_CSR_SIZE},
    {"sim_top.i_hdl_top.i_europa.u_aipu.u_l2_p_%lu.u_pctl",             2, 1, 1, 1, SYS_CFG_L2_MODULE_0_AO_CSR_BASE, SYS_CFG_L2_MODULE_0_AO_CSR_SIZE},
    // {"sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_graph_%lu.u_pctl",    4, 3, 2, 2, SYS_CFG_DDR_0_AO_CSR_BASE,       SYS_CFG_DDR_0_AO_CSR_SIZE},        // Activating fences fails
    // {"sim_top.i_hdl_top.i_europa.u_aipu.u_lpddr_p_ppp_%lu.u_pctl",      4, 3, 2, 2, SYS_CFG_DDR_4_AO_CSR_BASE,       SYS_CFG_DDR_4_AO_CSR_SIZE},        // Activating fences fails
    {"sim_top.i_hdl_top.i_europa.u_aipu.u_noc_top.u_sdma_%lu_p.u_pctl", 1, 1, 1, 1, SYS_CFG_SDMA_0_AO_CSR_BASE,      SYS_CFG_SDMA_0_AO_CSR_SIZE},       // n_pctl = 2
    {"sim_top.i_hdl_top.i_europa.u_aipu.u_dcd_p.u_pctl",                1, 2, 2, 2, SYS_CFG_DECODER_AO_CSR_BASE,     SYS_CFG_DECODER_AO_CSR_SIZE},
    {"sim_top.i_hdl_top.i_europa.u_aipu.u_pve_p_%lu.u_pctl",            1, 1, 1, 1, SYS_CFG_PVE_0_AO_CSR_BASE,       SYS_CFG_PVE_0_AO_CSR_SIZE}         // n_pctl = 2
};

char pctl_path[200];
char o_partition_rst_n_paths[8][200];
char i_noc_async_idle_val_paths[8][200];
uint64_t o_partition_rst_n;
uint64_t i_noc_async_idle_val;

int main()
{
    testcase_init();
    printf("Test starts!\n");

    // Go through all PCTL groups
    for(uint64_t i = 0; i < ARRAY_LENGTH(pctls); i++) {
        // Go through all PCTLs in one group
        for(uint64_t j = 0; j < pctls[i].n_pctl; j++) {
            /* Construct pctl uvm paths **********************************************************/
            sprintf(pctl_path,  pctls[i].path, j);
            printf("Testing: %s\n", pctl_path);

            for(uint64_t k = 0; k < pctls[i].n_resets; k++) {
                sprintf(o_partition_rst_n_paths[k], "%s%s[%lu]", pctl_path, ".o_partition_rst_n", k);
            }
            for(uint64_t k = 0; k < pctls[i].n_fences; k++) {
                sprintf(i_noc_async_idle_val_paths[k], "%s%s[%lu]", pctl_path, ".i_noc_async_idle_val", k);
            }

            /* Activate IP *********************************************************************
             * Clocks need to be present and device's resets removed.
             * https://doc.axelera.ai/ai-hw-team/triton/documentation/noc/noc-sw-guide/#boot-procedure
             * */
            for(uint64_t k = 0; k < pctls[i].n_resets; k++) {
                LOG_INFO("Removing reset %lu\n", k);
                CHECK_TRUE(pctlResetRemove((pctl_regs*)(pctls[i].base + j * pctls[i].offset), k) == 0, "Failed to remove the reset!");
            }
            for(uint64_t k = 0; k < pctls[i].n_fences; k++) {
                LOG_INFO("Removing fence %lu\n", k);
                CHECK_TRUE(pctlFenceRemove((pctl_regs*)(pctls[i].base + j * pctls[i].offset), k) == 0, "Failed to remove the fence!");
            }
#ifdef UVM_SW_IPC
            // Check if removed
            for(uint64_t k = 0; k < pctls[i].n_resets; k++) {
                o_partition_rst_n = uvm_sw_ipc_hdl_read(o_partition_rst_n_paths[k]);
                CHECK_TRUE(o_partition_rst_n == 1, "Reset %lu of %s not removed", k, pctl_path);
            }
            for(uint64_t k = 0; k < pctls[i].n_fences; k++) {
                i_noc_async_idle_val = uvm_sw_ipc_hdl_read(i_noc_async_idle_val_paths[k]);
                CHECK_TRUE(i_noc_async_idle_val == 0, "Fence %lu of %s not removed", k, pctl_path);
            }
#endif

            /* Deactivate IP ********************************************************************/
            for(uint64_t k = 0; k < pctls[i].n_fences; k++) {
                LOG_INFO("Activating fence %lu\n", k);
                CHECK_TRUE(pctlFenceActivate((pctl_regs*)(pctls[i].base + j * pctls[i].offset), k) == 0, "Failed to activate the fence!");
            }
            for(uint64_t k = 0; k < pctls[i].n_resets; k++) {
                LOG_INFO("Activating reset %lu\n", k);
                CHECK_TRUE(pctlResetActivate((pctl_regs*)(pctls[i].base + j * pctls[i].offset), k) == 0, "Failed to activate the reset!");
            }
#ifdef UVM_SW_IPC
            // Check if activated
            for(uint64_t k = 0; k < pctls[i].n_fences; k++) {
                i_noc_async_idle_val = uvm_sw_ipc_hdl_read(i_noc_async_idle_val_paths[k]);
                CHECK_TRUE(i_noc_async_idle_val == 1, "Fence %lu of %s not activated", k, pctl_path);
            }
            for(uint64_t k = 0; k < pctls[i].n_resets; k++) {
                o_partition_rst_n = uvm_sw_ipc_hdl_read(o_partition_rst_n_paths[k]);
                CHECK_TRUE(o_partition_rst_n == 0, "Reset %lu of %s not activated", k, pctl_path);
            }
#endif
        }
    }

    printf("Test ends!\n");
    return testcase_finalize();
}
