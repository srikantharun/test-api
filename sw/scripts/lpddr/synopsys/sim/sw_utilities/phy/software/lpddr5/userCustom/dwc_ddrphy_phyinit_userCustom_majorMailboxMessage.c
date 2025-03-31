// This is user-editable function.  User can edit this function according to their needs.
//
// The purpose of dwc_ddrphy_phyinit_userCustom_majorMailboxMessage() is to handle major
// mail box messages
//
// The default behavior of this function is to print commments relating to this process.
//
// User can chooose to leave this function as is, or implement mechanism
// to trigger mailbox poling event in simulation
// ====================================================================================

#include "dwc_ddrphy_phyinit.h"

#ifdef DWC_DDRPHY_PHYINIT_MAILBOX
void dwc_ddrphy_phyinit_userCustom_majorMailboxMessage(uint16_t message)
{
    dwc_ddrphy_phyinit_cmnt("0x%02x\n", message);
}
#endif // DWC_DDRPHY_PHYINIT_MAILBOX
