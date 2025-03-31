
/** \file
 *  \brief Header file for PhyInit
 */
#ifndef _DWC_DDRPHY_PHYINIT_H_
#define _DWC_DDRPHY_PHYINIT_H_

#include <stdio.h>
#include "dwc_ddrphy_phyinit_userCustom.h"
#include "dwc_ddrphy_phyinit_feature_defines.h"

/*! \def DWC_DDRPHY_PHYINIT_RID
 * cdefine for a PhyInit Revision ID
 */
#define DWC_DDRPHY_PHYINIT_RID 20240710

/// File pointer for out txtfile
extern FILE *outFilePtr;

/// stores input string from -comment_string
extern char *CmntStr;

/// stores input string from -apb_string
extern char *ApbStr;

/// < Current Number of S3 list registers saved.
extern int NumRegSaved;

/// Array of Address/value pairs used to store register values for the purpose of retention restore.
extern Reg_Addr_Val_t RetRegList[MAX_NUM_RET_REGS];

// Function definitions
int dwc_ddrphy_phyinit_setMb(phyinit_config_t *phyctx, int ps, char *field, int value);
int dwc_ddrphy_phyinit_softSetMb(phyinit_config_t *phyctx, int ps, char *field, int value);
void dwc_ddrphy_phyinit_initStruct(phyinit_config_t *phyctx);

#endif // _DWC_DDRPHY_PHYINIT_H_
