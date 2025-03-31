#pragma once

#include "lpddr_ctl_memorymap.h"
#include "lpddr_phy_memorymap.h"
#include <memorymap.h>
#include <regutils.h>
#include <stdbool.h>
#include <stdint.h>
#include <testutils.h>
#include <timer.h>

#define LPDDR_MODULE_NUM 0
#define LPDDR_MODULE_APB_RST_OFFSET 0x0
#define LPDDR_CTL_CORE_RST_OFFSET   0x4
#define LPDDR_PHY_RST_OFFSET        0x8
#define LPDDR_RESET_ASSERT true
#define LPDDR_RESET_DEASSERT false

// TODO: @rodrigo.borges - generate lpddr_ao_csr_memorymap.h
#define LPDDR_PPMU_ISOLATION_CONTROL_OFFSET 0x44
#define LPDDR_NOC_FENCE_ENABLE true
#define LPDDR_NOC_FENCE_DISABLE false

#define LPDDR_CSR_AXI_LOW_POWER_CONTROL_OFFSET 0x210
#define LPDDR_CSR_DDRC_LOW_POWER_CONTROL_OFFSET 0x214

// PCTL related methods
uintptr_t lpddrSysCfgGetRegOffset(unsigned int moduleNum);
void lpddrModuleApbReset(unsigned int moduleNum, bool resetAssert);
void lpddrCtlCoreReset(unsigned int moduleNum, bool resetAssert);
void lpddrPhyReset(unsigned int moduleNum, bool resetAssert);
void lpddrNocFenceTargHt(unsigned int moduleNum, bool enableFences);
void lpddrNocFenceTargCfg(unsigned int moduleNum, bool enableFences);
void lpddrAXILowPowerEnable(unsigned int moduleNum, bool enableLowPower, int idle_delay);
void lpddrDDRCLowPowerEnable(unsigned int moduleNum, bool enableLowPower, int idle_delay);

// Mode register access methods
void lpddrModeRegisterWrite(uint8_t mrAddress, uint8_t mrData);
void lpddrModeRegisterRead(uint8_t mrAddress);

uintptr_t lpddrCtlGetRegOffset(unsigned int moduleNum, uint64_t offset);
uintptr_t lpddrPhyGetRegOffset(unsigned int moduleNum, uint64_t offset);
void lpddrPhyWriteReg32(uint64_t offset, uint32_t value);
void lpddrCtlInit();
void lpddrCtlPostCfg();
void lpddrCtlPostPhyInit();
void lpddrPhyPostInit();
void lpddrCtlGroup3Registers(bool setRegs);
void lpddrSubsystemInit(bool lowPowerEnable);

// PHY related methods
void dwc_ddrphy_phyinit_userCustom_wait(uint32_t nDfiClks);
void dwc_ddrphy_phyinit_getMail(uint16_t* mail, uint16_t* data);
void dwc_ddrphy_phyinit_userCustom_G_waitFwDone();
void lpddrPhyInit_cpu_dpi_ss4_skiptrain();
